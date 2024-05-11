use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::*,
    plonk::*, poly::Rotation,
};

use super::is_zero::{IsZeroChip, IsZeroConfig};

#[derive(Debug, Clone)]
pub struct IsEqualConfig<F: FieldExt> {
    a: Column<Advice>,
    b: Column<Advice>,
    selector: Selector,
    a_equals_b: IsZeroConfig<F>,
}

pub struct IsEqualChip<F: FieldExt> {
    config: IsEqualConfig<F>,
}

impl<F: FieldExt> IsEqualChip<F> {
    pub fn construct(config: IsEqualConfig<F>) -> Self {
        Self { config }
    } 

    pub fn configure(meta: &mut ConstraintSystem<F>) -> IsEqualConfig<F> {
        let selector = meta.selector();
        let a = meta.advice_column();
        let b = meta.advice_column();
        let is_zero_advice_colum = meta.advice_column();

        let a_equals_b = IsZeroChip::configure(
            meta, 
            |meta| meta.query_selector(selector), 
            |meta| meta.query_advice(a, Rotation::cur()) - meta.query_advice(b, Rotation::cur()), 
            is_zero_advice_colum
        );
        // let is_equal = a_equals_b.is_zero_expr;

        meta.create_gate("Is Equal", |meta| {
            let s = meta.query_selector(selector);
            let a: Expression<F> = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());

            vec![s * (a - b)]
        });

        IsEqualConfig {
            a,
            b,
            selector,
            a_equals_b,
        }
    }

    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        a: Value<F>,
        b: Value<F>,
    ) -> Result<(), Error> {
        let is_zero_chip = IsZeroChip::construct(self.config.a_equals_b.clone());

        layouter.assign_region(|| "assign value", |mut region| {
            let offset = 0;
            self.config.selector.enable(&mut region, offset)?;
            region.assign_advice(|| "a", self.config.a, offset, || a)?;
            region.assign_advice(|| "b", self.config.b, offset, || b)?;
            is_zero_chip.assign(&mut region, offset, a - b)?;
            Ok(())
        })
    }
}

#[derive(Default)]
pub struct IsEqualCircuit<F> {
    a: Value<F>,
    b: Value<F>,
}

impl<F: FieldExt> Circuit<F> for IsEqualCircuit<F> {
    type Config = IsEqualConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        IsEqualChip::configure(meta)
    }

    fn synthesize(&self, config: Self::Config, layouter: impl Layouter<F>) -> Result<(), Error> {
        let chip = IsEqualChip::construct(config);
        chip.assign(layouter, self.a, self.b)
    }
}

#[cfg(test)]
mod test {
    use halo2_proofs::{circuit::Value, dev::MockProver, pasta::Fp};

    use super::IsEqualCircuit;

    #[test]
    fn test_is_equal() {
        let circuit = IsEqualCircuit {
            a: Value::known(Fp::from(42)),
            b: Value::known(Fp::from(42)),
        };

        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }
}