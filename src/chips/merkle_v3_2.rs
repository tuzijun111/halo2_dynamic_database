use super::hash_2::{self, Hash2Chip, Hash2Config};
use super::poseidon::{PoseidonChip, PoseidonConfig};
use halo2_gadgets::poseidon::{
    primitives::{self as poseidon, ConstantLength, P128Pow5T3 as OrchardNullifier, Spec},
    Hash,
};
use halo2_proofs::{
    arithmetic::{Field},
    circuit::*,
    // pasta::Fp,
    plonk::*,
    poly::Rotation,
};
use halo2curves::pasta::{pallas, vesta, EqAffine, Fp};

#[derive(Debug, Clone)]
pub struct MerkleTreeV3Config {
    pub advice: [Column<Advice>; 3],
    pub bool_selector: Selector,
    pub swap_selector: Selector,
    pub instance: Column<Instance>,
    pub poseidon_config: PoseidonConfig<3, 2, 2>,
}

#[derive(Debug, Clone)]
pub struct MerkleTreeV3Chip {
    config: MerkleTreeV3Config,
}

impl MerkleTreeV3Chip {
    pub fn construct(config: MerkleTreeV3Config) -> Self {
        Self { config }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<Fp>,
        advice: [Column<Advice>; 3],
        instance: Column<Instance>,
    ) -> MerkleTreeV3Config {
        let col_a = advice[0];
        let col_b = advice[1];
        let col_c = advice[2];
        let bool_selector = meta.selector();
        let swap_selector = meta.selector();
        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);

        // Enforces that c is either a 0 or 1.
        meta.create_gate("bool", |meta| {
            let s = meta.query_selector(bool_selector);
            let c = meta.query_advice(col_c, Rotation::cur());
            vec![s * c.clone() * (Expression::Constant(Fp::from(1)) - c.clone())]
        });

        // Enforces that if the swap bit is on, l=b and r=a. Otherwise, l=a and r=b.
        meta.create_gate("swap", |meta| {
            let s = meta.query_selector(swap_selector);
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());
            let l = meta.query_advice(col_a, Rotation::next());
            let r = meta.query_advice(col_b, Rotation::next());
            vec![
                s * (c * Expression::Constant(Fp::from(2)) * (b.clone() - a.clone())
                    - (l - a.clone())
                    - (b.clone() - r)),
            ]
        });

        MerkleTreeV3Config {
            advice: [col_a, col_b, col_c],
            bool_selector: bool_selector,
            swap_selector: swap_selector,
            instance: instance,
            poseidon_config: PoseidonChip::<OrchardNullifier, 3, 2, 2>::configure(meta),
        }
    }

    pub fn load_private(
        &self,
        mut layouter: impl Layouter<Fp>,
        input: Value<Fp>,
    ) -> Result<AssignedCell<Fp, Fp>, Error> {
        layouter.assign_region(
            || "load private",
            |mut region| {
                region.assign_advice(|| "private input", self.config.advice[0], 0, || input)
            },
        )
    }

    pub fn load_constant(
        &self,
        mut layouter: impl Layouter<Fp>,
        constant: Fp,
    ) -> Result<AssignedCell<Fp, Fp>, Error> {
        layouter.assign_region(
            || "load constant",
            |mut region| {
                region.assign_advice_from_constant(
                    || "constant value",
                    self.config.advice[0],
                    0,
                    constant,
                )
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<Fp>,
        cell: &AssignedCell<Fp, Fp>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }

    pub fn merkle_prove_layer(
        &self,
        mut layouter: impl Layouter<Fp>,
        digest: &AssignedCell<Fp, Fp>,
        element: Value<Fp>,
        index: Value<Fp>,
    ) -> Result<AssignedCell<Fp, Fp>, Error> {
        let (left, right) = layouter.assign_region(
            || "merkle_prove_leaf",
            |mut region| {
                // Row 0
                digest.copy_advice(|| "digest", &mut region, self.config.advice[0], 0)?;
                region.assign_advice(|| "element", self.config.advice[1], 0, || element)?;
                region.assign_advice(|| "index", self.config.advice[2], 0, || index)?;
                self.config.bool_selector.enable(&mut region, 0)?;
                self.config.swap_selector.enable(&mut region, 0)?;

                // Row 1
                let digest_value = digest.value().map(|x| x.to_owned());
                let (mut l, mut r) = (digest_value, element);
                index.map(|x| {
                    (l, r) = if x == Fp::zero() { (l, r) } else { (r, l) };
                });
                let left = region.assign_advice(|| "left", self.config.advice[0], 1, || l)?;
                let right = region.assign_advice(|| "right", self.config.advice[1], 1, || r)?;

                Ok((left, right))
            },
        )?;

        let poseidon_chip = PoseidonChip::<OrchardNullifier, 3, 2, 2>::construct(
            self.config.poseidon_config.clone(),
        );
        let digest: AssignedCell<Fp, Fp> = poseidon_chip.hash(layouter.namespace(|| "poseidon"), &[left, right])?;
        Ok(digest)
    }

    pub fn merkle_prove(
        &self,
        mut layouter: impl Layouter<Fp>,
        leaf: &AssignedCell<Fp, Fp>, // the first node
        elements: &Vec<Vec<Value<Fp>>>,
        indices: &Vec<Vec<Value<Fp>>>,
    ) -> Result<AssignedCell<Fp, Fp>, Error> {
        let mut leaf_or_digest = self.merkle_prove_layer(
            layouter.namespace(|| "merkle_prove_layer_0"),
            leaf,
            elements[0][0],
            indices[0][0],
        )?;
        for i in 0..elements.len(){
            let layers = elements[i].len();

            for j in 0..layers {
                // if i == 0 && j == 0{
                //     continue;
                // }
                leaf_or_digest = self.merkle_prove_layer(
                    layouter.namespace(|| format!("merkle_prove_layer_{}", j)),
                    &leaf_or_digest,
                    elements[i][j],
                    indices[i][j],
                )?;
            }
        }
        
        
        Ok(leaf_or_digest)
    }
}

#[derive(Default)]
struct MerkleTreeV3Circuit {
    pub leaf: Value<Fp>,
    pub elements: Vec<Vec<Value<Fp>>>,
    pub indices: Vec<Vec<Value<Fp>>>,
}

impl Circuit<Fp> for MerkleTreeV3Circuit {
    type Config = MerkleTreeV3Config;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let instance = meta.instance_column();
        MerkleTreeV3Chip::configure(meta, [col_a, col_b, col_c], instance)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        let chip = MerkleTreeV3Chip::construct(config);
        let leaf_cell = chip.load_private(layouter.namespace(|| "load leaf"), self.leaf)?;
        chip.expose_public(layouter.namespace(|| "public leaf"), &leaf_cell, 0)?;
        let digest = chip.merkle_prove(
            layouter.namespace(|| "merkle_prove"),
            &leaf_cell,
            &self.elements,
            &self.indices,
        )?;
        // chip.expose_public(layouter.namespace(|| "leaf"), &leaf_cell, 0)?;
        chip.expose_public(layouter.namespace(|| "public root"), &digest, 1)?;
        Ok(())
    }
}

mod tests {

    use crate::chips::poseidon;

    use super::MerkleTreeV3Circuit;
    use halo2_gadgets::poseidon::{
        primitives::{self as poseidon1, ConstantLength, P128Pow5T3 as OrchardNullifier, Spec},
        Hash,
    };
    use halo2_proofs::{circuit::Value, dev::MockProver};
    use halo2curves::pasta::{pallas, vesta, EqAffine, Fp};

    fn compute_merkle_root(elements: &Vec<Vec<u64>>, indices: &Vec<Vec<u64>>) -> Fp {
      
        let mut digest = Fp::from(elements[0][0].clone());
        let mut message: [Fp; 2];
        for i in 0..elements.len(){
            for j in 0..elements[i].len() {
                // if i == 0 && j == 0{
                //     continue;
                // }
                if indices[i][j] == 0 {
                    message = [digest, Fp::from(elements[i][j])];
                } else {
                    message = [Fp::from(elements[i][j]), digest];
                }

                digest = poseidon1::Hash::<_, OrchardNullifier, ConstantLength<2>, 3, 2>::init()
                    .hash(message);
            }
            
        }
        
        return digest;
    }

    #[test]
    fn test() {
        let leaf = 99u64;
        let M: u64 = 5;
        let n_vectors: usize = 1;
        let elements: Vec<Vec<u64>> = (0..n_vectors).map(|_| (1..=M).collect()).collect();
        let indices: Vec<Vec<u64>> = vec![vec![0u64; M as usize]; n_vectors];

        // let indices = vec![0u64, 1u64, 0u64, 0u64, 0u64];

        let digest = compute_merkle_root( &elements, &indices);

        println!("Digest: {:?}", elements);

        let leaf_fp = Value::known(Fp::from(leaf));
        let elements_fp: Vec<Vec<Value<Fp>>> = elements.iter()
        .map(|inner_vec| {
            inner_vec.iter()
                .map(|&num| Value::known(Fp::from(num)))
                .collect()
        })
        .collect();

        let indices_fp: Vec<Vec<Value<Fp>>> = indices.iter()
            .map(|inner_vec| {
                inner_vec.iter()
                    .map(|&num| Value::known(Fp::from(num)))
                    .collect()
            })
            .collect();
        

        let circuit = MerkleTreeV3Circuit {
            leaf: leaf_fp,
            elements: elements_fp,
            indices: indices_fp,
        };

        let correct_public_input = vec![Fp::from(leaf), Fp::from(digest)];
        let correct_prover = MockProver::run(
            11,
            &circuit,
            vec![correct_public_input.clone(), correct_public_input.clone()],
        )
        .unwrap();
        correct_prover.assert_satisfied();

       
    }
}