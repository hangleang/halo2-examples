use std::marker::PhantomData;

/// this helper checks that the value witnessed in a given cell is within a given range.
/// 
///     value       |       q_range_check
/// --------------------------------------------
///       v         |             1

use halo2_proofs::{
    arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation
};

#[derive(Debug, Clone)]
struct RangeCheckConfig<F: FieldExt, const RANGE: usize> {
    value: Column<Advice>,
    q_range_check: Selector,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const RANGE: usize> RangeCheckConfig<F, RANGE> {
    fn configure(meta: &mut ConstraintSystem<F>, value: Column<Advice>) -> Self {
        let q_range_check = meta.selector();

        // Range-Check gate
        // for a value `V` and a range `R`, check that `V` within range of `R`
        // V * (1 - V) * (2 - V) * ... * (R - 1 - V) == 0
        meta.create_gate("Range Check", |meta| {
            let q_range_check = meta.query_selector(q_range_check);
            let value = meta.query_advice(value, Rotation::cur());

            let range_check = |range: usize, value: Expression<F>| {
                assert!(range > 0);
                
                (0..range).fold(value.clone(), |acc, num| acc * (Expression::Constant(F::from(num as u64)) - value.clone()))
            };

            Constraints::with_selector(q_range_check, [("range check", range_check(RANGE, value))])
        });

        Self {
            value,
            q_range_check,
            _marker: PhantomData,
        }
    }

    fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        layouter.assign_region(|| "assign region", |mut region| {
            let offset = 0;
            self.q_range_check.enable(&mut region, offset)?;

            region.assign_advice(|| "value", self.value, offset, || value)?;
            Ok(())
        })
    }
}

#[derive(Default)]
struct RangeCheckCircuit<F: FieldExt, const RANGE: usize> {
    value: Value<Assigned<F>>,
}

impl<F: FieldExt, const RANGE: usize> Circuit<F> for RangeCheckCircuit<F, RANGE> {
    type Config = RangeCheckConfig<F, RANGE>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let value = meta.advice_column();
        RangeCheckConfig::configure(meta, value)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        config.assign(layouter.namespace(|| "assign value"), self.value)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use halo2_proofs::{circuit::Value, dev::{FailureLocation, MockProver, VerifyFailure}, pasta::Fp, plonk::Any};

    use super::RangeCheckCircuit;

    #[test]
    fn test_range_check1() {
        let k = 4;
        const RANGE: usize = 8;

        // satisfied tests
        for i in 0..RANGE {
            let circuit = RangeCheckCircuit::<Fp, RANGE> {
                value: Value::known(Fp::from(i as u64).into()),
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        // out-of-range test
        {
            let circuit = RangeCheckCircuit::<Fp, RANGE> {
                value: Value::known(Fp::from(RANGE as u64).into()),
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            assert_eq!(
                prover.verify(),
                Err(vec![VerifyFailure::ConstraintNotSatisfied {
                    constraint: ((0, "Range Check").into(), 0, "range check").into(),
                    location: FailureLocation::InRegion {
                        region: (0, "assign region").into(),
                        offset: 0
                    },
                    cell_values: vec![(((Any::Advice, 0).into(), 0).into(), "0x8".to_string())]
                }])
            )
        }
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_range_check_1() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("range-check-1-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root
            .titled("Range Check 1 Layout", ("sans-serif", 60))
            .unwrap();

        let circuit = RangeCheckCircuit::<Fp, 8> {
            value: Value::unknown(),
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(3, &circuit, &root)
            .unwrap();
    }
}
