use std::marker::PhantomData;

/// This helper checks that the value witnessed in a given cell is within a given range.
/// Depending on the range, this helper uses either a range-check expression (for small ranges),
/// or a lookup (for large ranges).
///
///        value     |    q_range_check    |   q_lookup  |  lookup_table  |
///       ----------------------------------------------------------------
///          v_0     |         1           |      0      |       0       |
///          v_1     |         0           |      1      |       1       |

use halo2_proofs::{
    arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation
};

#[derive(Debug, Clone)]
/// A range-constrained value in the circuit produced by the RangeCheckConfig.
struct RangeConstrained<F: FieldExt>(AssignedCell<Assigned<F>, F>);

/// A lookup table of values from 0..(1 << NUM_BITS).
/// 
#[derive(Debug, Clone)]
pub struct RangeTableConfig<F: FieldExt, const NUM_BITS: usize> {
    value: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const NUM_BITS: usize> RangeTableConfig<F, NUM_BITS> {
    fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let value = meta.lookup_table_column();

        Self {
            value,
            _marker: PhantomData,
        }
    }

    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(|| "load range check table", |mut table| {
            for value in 0..(1 << NUM_BITS) {
                table.assign_cell(|| "num bits", self.value, value, || Value::known(F::from(value as u64)))?;
            }
            Ok(())
        })
    }
}

#[derive(Debug, Clone)]
struct RangeCheckConfig<F: FieldExt, const RANGE: usize, const NUM_BITS: usize> {
    value: Column<Advice>,
    lookup_table: RangeTableConfig<F, NUM_BITS>,
    q_range_check: Selector,
    q_lookup: Selector,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const RANGE: usize, const NUM_BITS: usize> RangeCheckConfig<F, RANGE, NUM_BITS> {
    fn configure(meta: &mut ConstraintSystem<F>, value: Column<Advice>) -> Self {
        let q_range_check = meta.selector();
        let q_lookup = meta.complex_selector();
        let lookup_table = RangeTableConfig::configure(meta);

        // Range-Check gate
        // for a value `V` and a range `R`, check that `V` within range of `R`
        // V * (1 - V) * (2 - V) * ... * (R - 1 - V) == 0
        meta.create_gate("Range Check", |meta| {
            let q_range_check = meta.query_selector(q_range_check);
            let value = meta.query_advice(value, Rotation::cur());

            let range_check = |range: usize, value: Expression<F>| {
                assert!(range > 0);
                
                (1..range).fold(value.clone(), |acc, num| acc * (Expression::Constant(F::from(num as u64)) - value.clone()))
            };

            Constraints::with_selector(q_range_check, [("range check", range_check(RANGE, value))])
        });

        // lookup table
        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(q_lookup);
            let value = meta.query_advice(value, Rotation::cur());

            vec![(q_lookup * value, lookup_table.value)]
        });

        Self {
            value,
            lookup_table,
            q_range_check,
            q_lookup,
            _marker: PhantomData,
        }
    }

    fn assign_simple(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<Assigned<F>>,
    ) -> Result<RangeConstrained<F>, Error> {
        layouter.assign_region(|| "assign value for simple range check", |mut region| {
            let offset = 0;
            self.q_range_check.enable(&mut region, offset)?;

            region.assign_advice(|| "value", self.value, offset, || value).map(RangeConstrained)
        })
    }

    fn assign_lookup(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<Assigned<F>>,
    ) -> Result<RangeConstrained<F>, Error> {
        layouter.assign_region(|| "assign value for lookup range check", |mut region| {
            let offset = 0;
            self.q_lookup.enable(&mut region, offset)?;

            region.assign_advice(|| "value", self.value, offset, || value).map(RangeConstrained)
        })
    }
}

#[derive(Default)]
struct RangeCheckCircuit<F: FieldExt, const RANGE: usize, const NUM_BITS: usize> {
    value: Value<Assigned<F>>,
    lookup_value: Value<Assigned<F>>,
}

impl<F: FieldExt, const RANGE: usize, const NUM_BITS: usize> Circuit<F> for RangeCheckCircuit<F, RANGE, NUM_BITS> {
    type Config = RangeCheckConfig<F, RANGE, NUM_BITS>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let value = meta.advice_column();
        RangeCheckConfig::configure(meta, value)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        config.lookup_table.load(&mut layouter)?;

        config.assign_simple(layouter.namespace(|| "assign value"), self.value)?;
        config.assign_lookup(layouter.namespace(|| "assign lookup"), self.lookup_value)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use halo2_proofs::{circuit::Value, dev::{FailureLocation, MockProver, VerifyFailure}, pasta::Fp, plonk::Any};
    use super::RangeCheckCircuit;

    const K: u32 = 9;
    const RANGE: usize = 8;
    const NUM_BITS: usize = 4;

    #[test]
    fn test_range_check2() {

        // satisfied tests
        for i in 0..RANGE {
            for j in 0..(1 << NUM_BITS) {
                let circuit = RangeCheckCircuit::<Fp, RANGE, NUM_BITS> {
                    value: Value::known(Fp::from(i as u64).into()),
                    lookup_value: Value::known(Fp::from(j as u64).into())
                };
    
                let prover = MockProver::run(K, &circuit, vec![]).unwrap();
                prover.assert_satisfied();
            }
        }
    }

    #[test]
    fn test_out_of_range_check2() {
        let circuit = RangeCheckCircuit::<Fp, RANGE, NUM_BITS> {
            value: Value::known(Fp::from(RANGE as u64).into()),
            lookup_value: Value::known(Fp::from((1 << NUM_BITS) as u64).into()),
        };

        let prover = MockProver::run(K, &circuit, vec![]).unwrap();
        assert_eq!(
            prover.verify(),
            Err(vec![
                VerifyFailure::ConstraintNotSatisfied {
                    constraint: ((0, "Range Check").into(), 0, "range check").into(),
                    location: FailureLocation::InRegion {
                        region: (1, "assign value for simple range check").into(),
                        offset: 0
                    },
                    cell_values: vec![(((Any::Advice, 0).into(), 0).into(), format!("0x{:x}", RANGE))]
                },
                VerifyFailure::Lookup {
                    lookup_index: 0,
                    location: FailureLocation::InRegion {
                        region: (2, "assign value for lookup range check").into(),
                        offset: 0
                    }
                }
            ])
        )
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

        let circuit = RangeCheckCircuit::<Fp, RANGE, NUM_BITS> {
            value: Value::unknown(),
            lookup_value: Value::unknown(),
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(3, &circuit, &root)
            .unwrap();
    }
}
