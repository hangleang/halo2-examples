use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::*,
    plonk::*, poly::Rotation,
};

#[derive(Debug, Clone)]
pub struct IsZeroConfig<F: FieldExt> {
    pub value_inv: Column<Advice>,
    pub is_zero_expr: Expression<F>
}

pub struct IsZeroChip<F: FieldExt> {
    config: IsZeroConfig<F>,
}

impl<F: FieldExt> IsZeroChip<F> {
    pub fn construct(config: IsZeroConfig<F>) -> Self {
        Self {
            config
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>, 
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        value: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        value_inv: Column<Advice>,
    ) -> IsZeroConfig<F> {
        let mut is_zero_expr = Expression::Constant(F::zero());

        //
        // valid | value |  value_inv |  1 - value * value_inv | value * (1 - value* value_inv)
        // ------+-------+------------+------------------------+-------------------------------
        //  yes  |   x   |    1/x     |         0              |  0
        //  no   |   x   |    0       |         1              |  x
        //  yes  |   0   |    0       |         1              |  0
        //  yes  |   0   |    y       |         1              |  0
        //
        meta.create_gate("is_zero", |meta| {
            let value = value(meta);
            let q_enable = q_enable(meta);
            let value_inv = meta.query_advice(value_inv, Rotation::cur());

            is_zero_expr = Expression::Constant(F::one()) - value.clone() * value_inv;
            vec![q_enable * value * is_zero_expr.clone()]
        });

        IsZeroConfig {
            value_inv,
            is_zero_expr
        }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: Value<F>,
    ) -> Result<(), Error> {
        let value_inv = value.map(|v| v.invert().unwrap_or(F::zero()));
        region.assign_advice(|| "value invert", self.config.value_inv, offset, || value_inv)?;
        Ok(())
    }
}