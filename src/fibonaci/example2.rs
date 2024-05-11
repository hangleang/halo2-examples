use halo2_proofs::{arithmetic::Field, circuit::*, plonk::*, poly::Rotation};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
struct FiboConfig {
    pub advice: Column<Advice>,
    pub selector: Selector,
    pub instance: Column<Instance>,
}

struct FiboChip<F: Field> {
    config: FiboConfig,
    _marker: PhantomData<F>,
}

impl<F: Field> FiboChip<F> {
    pub fn construct(config: FiboConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: Column<Advice>,
        instance: Column<Instance>,
    ) -> FiboConfig {
        let selector = meta.selector();

        meta.enable_equality(advice);
        meta.enable_equality(instance);

        // 
        // advice | selector
        //   a    |    s
        //   b
        //   c
        //
        meta.create_gate("add", |meta| {
            let s = meta.query_selector(selector);
            let a = meta.query_advice(advice, Rotation::cur());
            let b = meta.query_advice(advice, Rotation::next());
            let c = meta.query_advice(advice, Rotation(2));
            vec![s * (a + b - c)]
        });

        FiboConfig {
            advice,
            selector,
            instance,
        }
    }

    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        rows: usize,
    ) -> Result<AssignedCell<F,F>, Error> {
        layouter.assign_region(
            || "fibonaci table",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;
                self.config.selector.enable(&mut region, 1)?;

                let mut a_cell = region.assign_advice_from_instance(
                    || "a", 
                    self.config.instance, 
                    0, 
                    self.config.advice, 
                    0,
                )?;
                let mut b_cell = region.assign_advice_from_instance(
                    || "b", 
                    self.config.instance, 
                    1, 
                    self.config.advice, 
                    1, 
                )?;

                for row in 2..rows {
                    if row < rows - 2 {
                        self.config.selector.enable(&mut region, row)?;
                    }

                    let c_cell = region.assign_advice(|| "c", self.config.advice, row, || a_cell.value().copied() + b_cell.value())?;

                    a_cell = b_cell;
                    b_cell = c_cell;
                }
            
                Ok(b_cell)
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: AssignedCell<F,F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
struct FiboCircuit<F: Field>(PhantomData<F>);

impl<F: Field> Circuit<F> for FiboCircuit<F> {
    type Config = FiboConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advice_col = meta.advice_column();
        let instance = meta.instance_column();
        FiboChip::configure(meta, advice_col, instance)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = FiboChip::construct(config);

        let out_cell = chip.assign(layouter.namespace(|| "fibonaci table"), 10)?;

        chip.expose_public(layouter.namespace(|| "out"), out_cell, 2)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::FiboCircuit;
    use std::marker::PhantomData;
    use halo2_proofs::{dev::MockProver, pasta::Fp};

    #[test]
    fn test_example2() {
        let k = 4;
        let a = Fp::from(1);
        let b = Fp::from(1);
        let out = Fp::from(55);

        let circuit = FiboCircuit(PhantomData);
        let mut public_input = vec![a, b, out];
        let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
        prover.assert_satisfied();

        // test fail proofs
        public_input[2] += Fp::one();
        let _prover = MockProver::run(k, &circuit, vec![public_input]).unwrap();
        // _prover.assert_satisfied();
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_example2() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("fib-2-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Fib 2 Layout", ("sans-serif", 60)).unwrap();

        let circuit = FiboCircuit::<Fp>(PhantomData);
        halo2_proofs::dev::CircuitLayout::default()
            .render(4, &circuit, &root)
            .unwrap();
    }
}
