use std::marker::PhantomData;

use ff::PrimeFieldBits;
use halo2_proofs::{
    arithmetic::FieldExt, 
    circuit::{floor_planner::V1, *}, plonk::*, poly::Rotation
};
use super::helpers;

/// This gadget range-constrains an element witnessed in the circuit to be N bits.
///
/// Internally, this gadget uses the `range_check` helper, which provides a K-bit
/// lookup table.
///
/// Given an element `value`, we use a running sum to break it into K-bit chunks.
/// Assume for now that N | K, and define C = N / K.
///
///     value = [b_0, b_1, ..., b_{N-1}]   (little-endian)
///           = c_0 + 2^K * c_1  + 2^{2K} * c_2 + ... + 2^{(C-1)K} * c_{C-1}
///
/// Initialise the running sum at
///                                 value = z_0.
///
/// Consequent terms of the running sum are z_{i+1} = (z_i - c_i) * 2^{-K}:
///
///                           z_1 = (z_0 - c_0) * 2^{-K}
///                           z_2 = (z_1 - c_1) * 2^{-K}
///                              ...
///                       z_{C-1} = c_{C-1}
///                           z_C = (z_{C-1} - c_{C-1}) * 2^{-K}
///                               = 0
///
/// One configuration for this gadget could look like:
///
///     | running_sum |  q_decompose  |  lookup_table  |
///     -----------------------------------------------
///     |     z_0     |       1       |       0       |
///     |     z_1     |       1       |       1       |
///     |     ...     |      ...      |      ...      |
///     |   z_{C-1}   |       1       |      ...      |
///     |     z_C     |       0       |      ...      |
///
/// Stretch task: use the tagged lookup table to constrain arbitrary bitlengths
/// (even non-multiples of K)

/// A lookup table of values from 0..(1 << NUM_BITS).
#[derive(Debug, Clone)]
pub struct RangeTableConfig<F: FieldExt, const RANGE: usize> {
    value: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const RANGE: usize> RangeTableConfig<F, RANGE> {
    fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let value: TableColumn = meta.lookup_table_column();

        Self {
            value,
            _marker: PhantomData,
        }
    }

    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(|| "load range check table", |mut table| {
            for value in 0..RANGE {
                table.assign_cell(|| "num bits", self.value, value, || Value::known(F::from(value as u64)))?;
            }
            Ok(())
        })
    }
}

#[derive(Debug, Clone)]
struct DecomposeConfig<F: FieldExt, const RANGE: usize> {
    // You'll need an advice column to witness your running sum;
    running_sum: Column<Advice>,
    // A selector to constrain the running sum;
    // A selector to lookup the K-bit chunks;
    q_decompose: Selector,
    // And of course, the K-bit lookup table
    lookup_table: RangeTableConfig<F, RANGE>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt + PrimeFieldBits, const RANGE: usize> DecomposeConfig<F, RANGE> {
    fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        // Create the needed columns and internal configs.
        let running_sum = meta.advice_column();
        let q_decompose = meta.complex_selector();
        let lookup_table = RangeTableConfig::configure(meta);

        // need a fixed column for `constrain_constant` used to enforce `z_C == 0`
        let constant = meta.fixed_column();
        meta.enable_constant(constant);
        meta.enable_equality(running_sum);

        // Range-constrain each K-bit chunk `c_i = z_i - z_{i+1} * 2^K` derived from the running sum.
        meta.lookup(|meta| {
            let q_decompose = meta.query_selector(q_decompose);
            
            let z_cur = meta.query_advice(running_sum, Rotation::cur());
            let z_next = meta.query_advice(running_sum, Rotation::next());
            let num_bits = (RANGE as i32 + 1).ilog2();

            // c_i = z_i - z_{i+1} * 2^K
            let chunk = z_cur - z_next * Expression::Constant(F::from(1 << num_bits));

            // when q_decompose = 0, define default_chunk
            let not_q_decompose = Expression::Constant(F::one()) - q_decompose.clone();
            let default_chunk = Expression::Constant(F::zero());

            // constraints expression
            let expr = q_decompose * chunk + not_q_decompose * default_chunk;
            vec![(expr, lookup_table.value)]
        });
        
        Self {
            running_sum,
            q_decompose,
            lookup_table,
            _marker: PhantomData,
        }
    }

    fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        value: AssignedCell<Assigned<F>, F>,
        num_bits: usize,
    ) -> Result<(), Error> {
        let lookup_num_bits = (RANGE as i32 + 1).ilog2() as usize;
        assert_eq!(num_bits % lookup_num_bits, 0);

        layouter.assign_region(|| "Decompose Region", |mut region| {
            let mut offset = 0;
            // 0. Copy in the witnessed `value` 
            let mut z = value.copy_advice(
                || "copy value to initialize running sum", &mut region, self.running_sum, offset)?;
            offset += 1;

            // 1. Compute the interstitial running sum values {z_0, ..., z_C}}
            let running_sum = value.value().map(|&v| helpers::compute_running_sum(v, num_bits, lookup_num_bits)).transpose_vec(num_bits / lookup_num_bits);

            // 2. Assign the running sum values
            for z_i in running_sum.into_iter() {
                z = region.assign_advice(|| format!("assign z_{}", offset), self.running_sum, offset, || z_i)?;
                offset += 1;
            }

            // 3. Make sure to enable the relevant selector on each row of the running sum
            for row in 0..(num_bits / lookup_num_bits) {
                self.q_decompose.enable(&mut region, row)?;
            }

            // 4. Constrain the final running sum `z_C` to be 0.
            region.constrain_constant(z.cell(), F::zero())
        })
    }
}

struct DecomposeRangeCheckCircuit<F, const LOOKUP_NUM_BITS: usize, const RANGE: usize> {
    value: Value<Assigned<F>>,
    num_bits: usize, // multiple of LOOKUP_NUM_BITS
}

impl<F: FieldExt + PrimeFieldBits, const LOOKUP_NUM_BITS: usize, const RANGE: usize> Circuit<F> for DecomposeRangeCheckCircuit<F, LOOKUP_NUM_BITS, RANGE> {
    type Config = DecomposeConfig<F, RANGE>;
    type FloorPlanner = V1;

    fn without_witnesses(&self) -> Self {
        Self {
            value: Value::unknown(),
            num_bits: self.num_bits,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        DecomposeConfig::configure(meta)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        config.lookup_table.load(&mut layouter)?;

        let value = layouter.assign_region(|| "witness region", |mut region| {
            region.assign_advice(|| "witness value", config.running_sum, 0, || self.value)
        })?;

        config.assign(layouter.namespace(|| "decompose value"), value, self.num_bits)
    }
}

#[cfg(test)]
mod test {
    use halo2_proofs::{circuit::Value, dev::MockProver, pasta::Fp};
    use rand;

    use super::DecomposeRangeCheckCircuit;

    const K: u32 = 9;
    const NUM_BITS: usize = 8;
    const RANGE: usize = 256;

    #[test]
    fn test_decompose_range_check1() {
        let value: u64 = rand::random();
        let circuit = DecomposeRangeCheckCircuit::<Fp, NUM_BITS, RANGE> {
            value: Value::known(Fp::from(value).into()),
            num_bits: 64,
        };
        let prover = MockProver::run(K, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_decompose_1() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("decompose-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root
            .titled("Decompose Range Check Layout", ("sans-serif", 60))
            .unwrap();

        let circuit = DecomposeRangeCheckCircuit::<Fp, NUM_BITS, RANGE> {
            value: Value::unknown(),
            num_bits: 64,
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(9, &circuit, &root)
            .unwrap();
    }
}