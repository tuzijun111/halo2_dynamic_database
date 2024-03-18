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
        let digest = poseidon_chip.hash(layouter.namespace(|| "poseidon"), &[left, right])?;
        Ok(digest)
    }

    pub fn merkle_prove(
        &self,
        mut layouter: impl Layouter<Fp>,
        leaf: &AssignedCell<Fp, Fp>,
        elements: &Vec<Value<Fp>>,
        indices: &Vec<Value<Fp>>,
    ) -> Result<AssignedCell<Fp, Fp>, Error> {
        let layers = elements.len();
        let mut leaf_or_digest = self.merkle_prove_layer(
            layouter.namespace(|| "merkle_prove_layer_0"),
            leaf,
            elements[0],
            indices[0],
        )?;
        for i in 1..layers {
            leaf_or_digest = self.merkle_prove_layer(
                layouter.namespace(|| format!("merkle_prove_layer_{}", i)),
                &leaf_or_digest,
                elements[i],
                indices[i],
            )?;
        }
        Ok(leaf_or_digest)
    }

    pub fn poseidon_hash_array(
        &self,
        mut layouter: impl Layouter<Fp>,
        values: &[AssignedCell<Fp, Fp>],
    ) -> Result<AssignedCell<Fp, Fp>, Error> {
        const CHUNK_SIZE: usize = 256;
        let chunks = values.chunks(CHUNK_SIZE);
        let mut chunk_hashes = Vec::with_capacity(chunks.len());
    
        for chunk in chunks {
            let chunk_hash = self.poseidon_hash_chunk(layouter.namespace(|| "poseidon hash chunk"), chunk)?;
            chunk_hashes.push(chunk_hash);
        }
    
        let mut root = chunk_hashes[0].clone();
        for (i, chunk_hash) in chunk_hashes.iter().skip(1).enumerate() {
            root = self.merkle_prove_layer(
                layouter.namespace(|| format!("merkle prove layer {}", i)),
                &root,
                chunk_hash.value().copied(),
                Value::known(Fp::from(i as u64)),
            )?;
        }
    
        Ok(root)
    }
    
    fn poseidon_hash_chunk(
        &self,
        mut layouter: impl Layouter<Fp>,
        values: &[AssignedCell<Fp, Fp>],
    ) -> Result<AssignedCell<Fp, Fp>, Error> {
        let poseidon_chip = PoseidonChip::<OrchardNullifier, 3, 2, 2>::construct(self.config.poseidon_config.clone());
    
        let mut padded_values = vec![values[0].clone(); 256];
        padded_values[..values.len()].clone_from_slice(values);
    
        let chunk_array = [padded_values[0].clone(), padded_values[1].clone()];
        poseidon_chip.hash(layouter.namespace(|| "poseidon hash chunk"), &chunk_array)
    }
    
    
}

#[derive(Default)]

struct MerkleTreeV3Circuit {
    pub values: Vec<Value<Fp>>,
    pub root: Value<Fp>,
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

        // Load and assign the input values
        let values_cells: Vec<_> = self
            .values
            .iter()
            .map(|value| chip.load_private(layouter.namespace(|| "load value"), *value))
            .collect::<Result<_, _>>()?;

        // Compute the Poseidon hash root
        let root = chip.poseidon_hash_array(layouter.namespace(|| "poseidon hash"), &values_cells)?;

        // Expose the root as a public input
        chip.expose_public(layouter.namespace(|| "public root"), &root, 0)?;

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

    fn compute_expected_root(values: &[Fp]) -> Fp {
        const CHUNK_SIZE: usize = 256;
        let chunks = values.chunks(CHUNK_SIZE);
        let mut chunk_hashes = Vec::with_capacity(chunks.len());

        for chunk in chunks {
            let mut padded_chunk = vec![Fp::zero(); 256];
            padded_chunk[..chunk.len()].copy_from_slice(chunk);
            let chunk_array: [Fp; 2] = [padded_chunk[0], padded_chunk[1]];
            let chunk_hash = poseidon1::Hash::<_, OrchardNullifier, ConstantLength<2>, 3, 2>::init().hash(chunk_array);
            chunk_hashes.push(chunk_hash);
        }

        let mut root = chunk_hashes[0];
        for chunk_hash in chunk_hashes.iter().skip(1) {
            let left = root;
            let right = *chunk_hash;
            let message = [left, right];
            root = poseidon1::Hash::<_, OrchardNullifier, ConstantLength<2>, 3, 2>::init().hash(message);
        }

        root
    }

 
    #[test]
    fn test() {
        let values: Vec<_> = (0..4).map(|i| Fp::from(i as u64)).collect();
        let expected_root = compute_expected_root(&values);

        let circuit = MerkleTreeV3Circuit {
            values: values.iter().map(|&v| Value::known(v)).collect(),
            root: Value::known(expected_root),
        };

        let public_inputs = vec![vec![expected_root]];
        let prover = MockProver::run(15, &circuit, public_inputs.clone()).unwrap();
        prover.assert_satisfied();

        assert_eq!(prover.verify(), Ok(()));
    }
}
