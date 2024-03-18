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
    pub advice: [Column<Advice>; 2],

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
        advice: [Column<Advice>; 2],
        instance: Column<Instance>,
    ) -> MerkleTreeV3Config {
        let col_a = advice[0];
        let col_b = advice[1];

    
        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
      
        meta.enable_equality(instance);

       

        MerkleTreeV3Config {
            advice: [col_a, col_b],
     
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
      
    ) -> Result<AssignedCell<Fp, Fp>, Error> {
        let (left, right) = layouter.assign_region(
            || "merkle_prove_leaf",
            |mut region| {
                // Row 0
                digest.copy_advice(|| "digest", &mut region, self.config.advice[0], 0)?;
                region.assign_advice(|| "element", self.config.advice[1], 0, || element)?;

                // Row 1
                let digest_value = digest.value().map(|x| x.to_owned());
                let (mut l, mut r) = (digest_value, element);
       
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
        // elements2: &Vec<Value<Fp>>,
    ) -> Result<AssignedCell<Fp, Fp>, Error> {
        let layers = elements.len();
        let mut leaf_or_digest = self.merkle_prove_layer(
            layouter.namespace(|| "merkle_prove_layer_0"),
            leaf,
            elements[0],      
        )?;
        for i in 2..layers {
            leaf_or_digest = self.merkle_prove_layer(
                layouter.namespace(|| format!("merkle_prove_layer_{}", i)),
                &leaf_or_digest,
                elements[i],
            
            )?;
        }
        
        
        Ok(leaf_or_digest)
    }
}

#[derive(Default)]
struct MerkleTreeV3Circuit {
    // pub leaf: Value<Fp>,
    pub elements: Vec<Value<Fp>>,
    pub elements2: Vec<Value<Fp>>,  
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
     
        let instance = meta.instance_column();
        MerkleTreeV3Chip::configure(meta, [col_a, col_b], instance)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        let chip = MerkleTreeV3Chip::construct(config);
        let leaf_cell = chip.load_private(layouter.namespace(|| "load leaf"), self.elements[0])?;
        // chip.expose_public(layouter.namespace(|| "public leaf"), &leaf_cell, 0)?;
        let digest = chip.merkle_prove(
            layouter.namespace(|| "merkle_prove"),
            &leaf_cell,
            &self.elements,
        )?;

        chip.expose_public(layouter.namespace(|| "public root"), &digest, 0)?;
        let digest = chip.merkle_prove(
            layouter.namespace(|| "merkle_prove"),
            &leaf_cell,
            &self.elements2,
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
    
    // fn compute_merkle_root(leaf: &u64, elements: &Vec<u64>, elements2: &Vec<u64>) -> Fp {
    fn compute_merkle_root(elements: &Vec<u64>, elements2: &Vec<u64>) -> Vec<Fp> {
        let mut digests = Vec::new();
        let k = elements.len();
        let mut digest = Fp::from(elements[0].clone());
        let mut message: [Fp; 2];
        for i in 0..k {        
            message = [digest, Fp::from(elements[i])];
           
            digest = poseidon1::Hash::<_, OrchardNullifier, ConstantLength<2>, 3, 2>::init()
                .hash(message);
        }
        digests.push(digest);
        // elements2
        let k = elements2.len();
        let mut digest = Fp::from(elements2[0].clone());
        let mut message: [Fp; 2];
        for i in 0..k {        
            message = [digest, Fp::from(elements2[i])];
           
            digest = poseidon1::Hash::<_, OrchardNullifier, ConstantLength<2>, 3, 2>::init()
                .hash(message);
        }
        digests.push(digest);

        return digests;
    }

    #[test]
    fn test() {
        const M: u64 = 24;
        let elements: Vec<u64> = (1..=M).collect();
        let elements2: Vec<u64> = (1..=M).collect();

        // let digest = compute_merkle_root(&leaf, &elements, &elements2);
        let digest = compute_merkle_root(&elements, &elements2);

        let elements_fp: Vec<Value<Fp>> = elements
            .iter()
            .map(|x| Value::known(Fp::from(x.to_owned())))
            .collect();

        let elements_fp2: Vec<Value<Fp>> = elements2
            .iter()
            .map(|x| Value::known(Fp::from(x.to_owned())))
            .collect();
       
        let circuit = MerkleTreeV3Circuit {
            elements: elements_fp,  
            elements2: elements_fp2,        
        };

        let correct_public_input = vec![Fp::from(digest[0]), Fp::from(digest[1])];
        let correct_prover = MockProver::run(
            11,
            &circuit,
            vec![correct_public_input.clone(), correct_public_input.clone()],
        )
        .unwrap();
        correct_prover.assert_satisfied();


    }
}