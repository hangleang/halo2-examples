use ff::PrimeFieldBits;
use halo2_proofs::{arithmetic::FieldExt, plonk::Assigned};

pub(super) fn lebs2ip(bits: &[bool]) -> u64 {
    assert!(bits.len() <= 64);
    bits.iter()
        .enumerate()
        .fold(0u64, |acc, (i, b)| acc + if *b { 1 << i } else { 0 })
}

// Function to compute the interstitial running sum values {z_1, ..., z_C}}
pub(super) fn compute_running_sum<F: FieldExt + PrimeFieldBits>(
    value: Assigned<F>,
    num_bits: usize,
    lookup_num_bits: usize,
) -> Vec<Assigned<F>> {
    let mut running_sum = vec![];
    let mut z = value;

    // Get the little-endian bit representation of `value`.
    let value: Vec<_> = value
        .evaluate()
        .to_le_bits()
        .iter()
        .by_vals()
        .take(num_bits)
        .collect();
    for chunk in value.chunks(lookup_num_bits) {
        let chunk = Assigned::from(F::from(lebs2ip(chunk)));
        // z_{i+1} = (z_i - c_i) * 2^{-K}:
        z = (z - chunk) * Assigned::from(F::from(1u64 << lookup_num_bits)).invert();
        running_sum.push(z);
    }

    assert_eq!(running_sum.len(), num_bits / lookup_num_bits);
    running_sum
}