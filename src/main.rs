use std::sync::Arc;

use ark_ff::{AdditiveGroup, BigInt, FftField, Field, Fp, PrimeField, Zero};
use ark_ff::fields::{Fp64, MontBackend, MontConfig};
use ark_ff::UniformRand;
use ark_ff::BigInteger;
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, Polynomial};

use rs_merkle::{MerkleTree, MerkleProof, Hasher, algorithms::Sha256};

#[derive(MontConfig)]
#[modulus = "18446744069414584321"] // p = 2^64 - 2^32 + 1
#[generator = "7"]
pub struct FConfig;

pub type F = Fp64<MontBackend<FConfig, 1>>;


//TODO add ZK option
#[derive(Debug)]
pub struct FriParams {
    n: u32,
    eta: u32,
    two_to_the_eta: usize,
    rate_parameter: u32,
    num_rounds: usize,
    k: Vec<u32>,
    smooth_multiplicative_subgroup: Vec<Vec<F>>,
    generator: Vec<F>,
    q: DensePolynomial<F>,
}

impl FriParams {
    pub fn new(eta: u32, rate_parameter: u32, degree_log_bound: u32) -> Self {

        let n = degree_log_bound + rate_parameter;
        assert!(n <= F::TWO_ADICITY, "log degree + rate parameter must be less than or equal to {}", F::TWO_ADICITY);
        let num_rounds = (degree_log_bound / eta) as usize;

        let two_to_the_eta: usize = 1 << eta;


        // smooth_multiplicative_subgroup[i] is the subgroup used in the i-th round, implemented as a Vec.
        // k[i] is the integer such that |smooth_multiplicative_subgroup[i]| = 2^{k[i]}.
        // generator[i] is a generator of smooth_multiplicative_subgroup[i].
        let mut smooth_multiplicative_subgroup: Vec<Vec<F>> = vec![];
        let mut k: Vec<u32> = vec![];
        let mut generator: Vec<F> = vec![];

        // As it turns out, the generator of L[0] is generated for us.
        let mut generator_i = FConfig::TWO_ADIC_ROOT_OF_UNITY.pow(BigInt::<1>::from(2_u64.pow(F::TWO_ADICITY - n)));
    
        for i in 0..=num_rounds {
            let k_i = n - (i as u32) * eta;
            let smooth_multiplicative_subgroup_i_order = 2_u64.pow(k_i);
            let mut smooth_multiplicative_subgroup_i = Vec::<F>::new();


            // Add all the elements of L[i] to the set. We do this by starting with 1 and repeatedly multiplying by the generator.
            let mut smooth_multiplicative_subgroup_i_element = F::ONE;
            for j in 0..smooth_multiplicative_subgroup_i_order {
                smooth_multiplicative_subgroup_i.push(smooth_multiplicative_subgroup_i_element);
                smooth_multiplicative_subgroup_i_element = smooth_multiplicative_subgroup_i_element * generator_i;
            }

            k.push(k_i);
            smooth_multiplicative_subgroup.push(smooth_multiplicative_subgroup_i);
            generator.push(generator_i);

            generator_i = generator_i.pow(BigInt::<1>::from(two_to_the_eta as u32));
        }

        // Set q(X) = X^{2^eta}
        let mut coefficient_vector = vec![F::ZERO; two_to_the_eta];
        coefficient_vector.push(F::ONE);
        let q = DensePolynomial::<F>::from_coefficients_vec(coefficient_vector);


        FriParams {
            n,
            eta,
            two_to_the_eta,
            rate_parameter,
            num_rounds,
            k,
            smooth_multiplicative_subgroup,
            generator,
            q,
        }
    }
}
pub struct FriProver {
    params: Arc<FriParams>,
    f: Vec<DensePolynomial<F>>,
    f_merkle_tree: Vec<MerkleTree<Sha256>>,
}

impl FriProver {
    fn new(params: Arc<FriParams>, polynomial: DensePolynomial<F>) -> FriProver {
        let mut prover = FriProver {
            params,
            f: vec![polynomial],
            f_merkle_tree: vec![]
        };
        prover.f_merkle_tree.push(prover.commit_polynomial(&prover.f[0], &prover.params.smooth_multiplicative_subgroup[0]));
        prover
    }

    /// Perform a single polynomial folding step using the provided verifier challenge.
    /// Example: with an eta value of 1 and a verifier challenge of 3, running this on the polynomial
    /// 1 + 2x + 3x^2 + 4x^3 should return (1 + 3x) + 3*(2 + 4x) = 7 + 15x.
    fn fold_polynomial(&self, polynomial: &DensePolynomial<F>, verifier_challenge: F) -> DensePolynomial<F> {

        // Write the input polynomial in the form f(x) = f_0(x^{2^\eta}) + xf_1(x^{2^\eta}) + ... + x^{2^\eta - 1}f_{2^\eta - 1}(x^{2^\eta})
        let mut sub_polynomials_coefficients: Vec<Vec<F>> = (0..self.params.two_to_the_eta).map(|_| vec![]).collect();

        for (i, coeff) in polynomial.coeffs().iter().enumerate() {
            sub_polynomials_coefficients[i % self.params.two_to_the_eta].push(*coeff);
        }
        
        let sub_polynomials: Vec<DensePolynomial<F>> = sub_polynomials_coefficients.into_iter().map(
            |coeffs| DensePolynomial::from_coefficients_vec(coeffs)
        ).collect();
    
        // Compute f_0(x) + vf_1(x) + ... + v^{2^\eta - 1}f_{2^\eta - 1}(x), where v is the verifier challenge
        let mut verifier_challenge_to_the_i = F::ONE;
        let mut folded_polynomial = DensePolynomial::<F>::zero();
        for sub_polynomial in sub_polynomials {
            folded_polynomial = folded_polynomial + sub_polynomial * verifier_challenge_to_the_i;
            verifier_challenge_to_the_i *= verifier_challenge;
        }
        folded_polynomial
    }


    /// Create a merkle tree and merkle proofs corresponding to the evaluations of a given polynomial
    /// at every point in the given domain. depth is the depth of the resulting merkle tree, so
    /// we must have 2^depth >= |domain|.
    fn commit_polynomial(&self, polynomial: &DensePolynomial<F>, domain: &Vec<F>) -> MerkleTree<Sha256> {

        // NOT ZERO KNOWLEDGE
        // values is list where the entries are of the form hash(x, f(x)) for each x in the domain
        let values = domain.into_iter().map(
            |x| value_to_merkle_leaf(&polynomial, x)
        ).collect::<Vec<[u8; 32]>>();
        
        let merkle_tree = MerkleTree::<Sha256>::from_leaves(&values);
        merkle_tree
    }

    fn execute_prover_round(round_index: usize, verifier_challenge: F){
        panic!("Not implemented");
    }
}




/// Deterministic function used to deterministically convert the value of a polynomial at a point
/// to a format suitable for insertion in a Merkle tree.
fn value_to_merkle_leaf(polynomial: &DensePolynomial<F>, point: &F ) -> [u8; 32] {
    Sha256::hash(
        vec![*point, polynomial.evaluate(point)].into_iter().flat_map(
            |value| value.into_bigint().to_bytes_be()
        ).collect::<Vec<u8>>().as_slice()
    )
}









fn main() {
    let mut rng = ark_std::test_rng();
    let a = F::rand(&mut rng);
    println!("a: {}", a);
    let params = FriParams::new(2, 2, 4);
    println!("params.q: {:?}", params.q);
    println!("params: {:?}", params);
}

#[cfg(test)]
pub mod tests {
    use super::*;


    fn create_test_prover(polynomial: DensePolynomial<F>) -> (FriProver, Arc<FriParams>) {
        let eta = 1;
        let rate_parameter = 2;
        let degree_log_bound = 3;
        let params = Arc::new(FriParams::new(eta, rate_parameter, degree_log_bound));
        
        let prover = FriProver::new(params.clone(), polynomial.clone());
        (prover, params)
    }

    #[test]
    fn test_polynomial_folding(){
        
        let polynomial = DensePolynomial::<F>::from_coefficients_vec(vec![F::from(1), F::from(2), F::from(3), F::from(4)]);
        let (prover, _) = create_test_prover(polynomial);
        let verifier_challenge = F::from(3);
        let result = prover.fold_polynomial(&prover.f[0], verifier_challenge);
        let expected = DensePolynomial::<F>::from_coefficients_vec(vec![F::from(7), F::from(15)]);
        println!("Result: {:?}", result);
        //println!("params: {:?}", prover.params);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_polynomial_commitment(){
        let polynomial = DensePolynomial::<F>::from_coefficients_vec(vec![F::from(1), F::from(2), F::from(3), F::from(4)]);
        let (prover, _) = create_test_prover(polynomial);
        let merkle_tree = prover.commit_polynomial(&prover.f[0], &prover.params.smooth_multiplicative_subgroup[0]);
        let proof = merkle_tree.proof(&[0]);
        let root = merkle_tree.root().expect("Merkle tree did not return root");
        let expected_leaf = value_to_merkle_leaf(&prover.f[0], &F::from(1));
        let unexpected_leaf = value_to_merkle_leaf(&prover.f[0], &F::from(2));
        assert!(proof.verify(root, &[0], &[expected_leaf], merkle_tree.leaves_len()));
        assert!(! proof.verify(root, &[0], &[unexpected_leaf], merkle_tree.leaves_len()));
    }
}



