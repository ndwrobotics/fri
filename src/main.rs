use std::iter::Sum;
use std::sync::Arc;

use ark_ff::{AdditiveGroup, BigInt, FftField, Field, Fp, PrimeField, Zero};
use ark_ff::fields::{Fp64, MontBackend, MontConfig};
use ark_ff::UniformRand;
use ark_ff::BigInteger;
use ark_poly::univariate::DensePolynomial;
use ark_poly::{evaluations, DenseUVPolynomial, Polynomial};

use ark_std::rand::rngs::StdRng;
use ark_std::rand::{Rng, SeedableRng};
use rs_merkle::{MerkleTree, MerkleProof, Hasher, algorithms::Sha256};

use rand_core::{TryRngCore, OsRng};

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
    num_repetitions: usize,
    degree_log_bound: u32,
    two_to_the_eta: usize,
    rate_parameter: u32,
    num_rounds: usize,
    k: Vec<u32>,
    smooth_multiplicative_subgroup: Vec<Vec<F>>,
    homomorphism_kernel: Vec<F>,
    homomorphism_kernel_generator: F,
    generator: Vec<F>,
    q: DensePolynomial<F>,
}

impl FriParams {
    pub fn new(eta: u32, rate_parameter: u32, degree_log_bound: u32, num_repetitions: usize) -> Self {

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

        // Set homomoprhism_kernel to be the set of elements annihilated by q
        let homomorphism_kernel_generator = FConfig::TWO_ADIC_ROOT_OF_UNITY.pow(BigInt::<1>::from(2_u64.pow(F::TWO_ADICITY - eta)));
        let mut homomorphism_kernel_element = F::ONE;
        let mut homomorphism_kernel = Vec::new();
        for i in 0..two_to_the_eta {
            homomorphism_kernel.push(homomorphism_kernel_element);
            homomorphism_kernel_element = homomorphism_kernel_element * homomorphism_kernel_generator;
        }

        FriParams {
            n,
            eta,
            num_repetitions,
            degree_log_bound,
            two_to_the_eta,
            rate_parameter,
            num_rounds,
            k,
            smooth_multiplicative_subgroup,
            homomorphism_kernel,
            homomorphism_kernel_generator,
            generator,
            q,
        }
    }
}
pub struct FriProver {
    params: Arc<FriParams>,
    f: Vec<DensePolynomial<F>>,
    f_merkle_tree: Vec<MerkleTree<Sha256>>,
    f_evaluation: Vec<Vec<F>>,
}

impl FriProver {
    /// Create a new Fri prover, following the given Fri params, to perform a proof on the given polynomial.
    fn new(params: Arc<FriParams>, polynomial: DensePolynomial<F>) -> FriProver {

        assert!(polynomial.degree() < (1 << params.degree_log_bound));

        let mut prover = FriProver {
            params,
            f: vec![polynomial],
            f_merkle_tree: vec![],
            f_evaluation: Vec::new(),
        };
        let (f_evaluation_0, f_merkle_tree_0) = prover.commit_polynomial(&prover.f[0], &prover.params.smooth_multiplicative_subgroup[0]);
        prover.f_merkle_tree.push(f_merkle_tree_0);
        prover.f_evaluation.push(f_evaluation_0);
        prover
    }

    /// Perform a single polynomial folding step using the provided verifier challenge.
    /// Example: with an eta value of 1 and a verifier challenge of 3, running this on the polynomial
    /// 1 + 2x + 3x^2 + 4x^3 should return (1 + 3x) + 3*(2 + 4x) = 7 + 15x.
    fn fold_polynomial(&self, polynomial: &DensePolynomial<F>, folding_challenge: F) -> DensePolynomial<F> {

        // Write the input polynomial in the form f(x) = f_0(x^{2^\eta}) + xf_1(x^{2^\eta}) + ... + x^{2^\eta - 1}f_{2^\eta - 1}(x^{2^\eta})
        let mut sub_polynomials_coefficients: Vec<Vec<F>> = (0..self.params.two_to_the_eta).map(|_| vec![]).collect();

        for (i, coeff) in polynomial.coeffs().iter().enumerate() {
            sub_polynomials_coefficients[i % self.params.two_to_the_eta].push(*coeff);
        }
        
        let sub_polynomials: Vec<DensePolynomial<F>> = sub_polynomials_coefficients.into_iter().map(
            |coeffs| DensePolynomial::from_coefficients_vec(coeffs)
        ).collect();
    
        // Compute f_0(x) + vf_1(x) + ... + v^{2^\eta - 1}f_{2^\eta - 1}(x), where v is the verifier challenge
        let mut folding_challenge_to_the_i = F::ONE;
        let mut folded_polynomial = DensePolynomial::<F>::zero();
        for sub_polynomial in sub_polynomials {
            folded_polynomial = folded_polynomial + sub_polynomial * folding_challenge_to_the_i;
            folding_challenge_to_the_i *= folding_challenge;
        }
        folded_polynomial
    }


    /// Create a merkle tree and merkle proofs corresponding to the evaluations of a given polynomial
    /// at every point in the given domain.
    fn commit_polynomial(&self, polynomial: &DensePolynomial<F>, domain: &Vec<F>) -> (Vec<F>, MerkleTree<Sha256>) {

        // evaluations is a list where the i-th entry is f(generator^i)
        let evaluations: Vec<F> = domain.into_iter().map(
            |x| polynomial.evaluate(x)
        ).collect();


        // NOT ZERO KNOWLEDGE
        // values is list where the i-th entry is hash(f(generator^i))
        let values = evaluations.iter().map(
            |x| value_to_merkle_leaf(x)
        ).collect::<Vec<[u8; 32]>>();
        
        let merkle_tree = MerkleTree::<Sha256>::from_leaves(&values);
        (evaluations, merkle_tree)
    }

    /// Given an index i, open the merkle tree commitment for polynomial i at a particular set of indices.
    /// Recall that this merkle tree contains commitments to the values of f[i](gen[i]^0), f[i](gen[i]^1), ... in that order.
    /// We return a vector of values of the polynomial at the values gen[i]^{exponent_offset}gen^0, gen[i]^{exponent_offset}gen^1, ...
    /// in that order, where gen is the homomorphism_kernel generator. We also return the corresponding merkle proof.
    /// In summary, this returns an opening the polynomial on a given coset of the homomorphism_kernel, in the most natural order.
    fn open_polynomial(&self, index: usize, exponent_offset: usize) -> (Vec<F>, MerkleProof<Sha256>) {
        // We wish to open this tree on the coset of homomorphism_kernel with offset exponent_offset.
        
        // Recall that the i-th smooth multiplicative subgroup has order 2^{k[i]}, while homomorphism_kernel has order 2^eta.
        let step_size = 2usize.pow(self.params.k[index] - self.params.eta);
        let exponents: Vec<usize> = (0..self.params.two_to_the_eta).map(
            |x| (exponent_offset + x * step_size) % (2usize.pow(self.params.k[index]))
        ).collect();

        println!("Calculated exponents for polynomial {index}: {:?}", exponents);

        let coset_evaluations = exponents.iter().map(
            |exponent| self.f_evaluation[index][*exponent]
        ).collect();

        println!("Calculated coset evaluations for polynomial {index}: {:?}", coset_evaluations);

        let merkle_proof = self.f_merkle_tree[index].proof(&exponents);
        return (coset_evaluations, merkle_proof);
    }

    fn execute_prover_commit_round(&mut self, round_index: usize, folding_challenge: Option<F>) -> [u8; 32] {

        println!("Prover round: {}", round_index);
        let polynomial_commitment;
        if round_index == 0 {
            polynomial_commitment = self.f_merkle_tree[0].root().unwrap();
        } else {
            let folded_polynomial = self.fold_polynomial(&self.f[round_index-1], folding_challenge.unwrap());
        println!("Folded polynomial: {:?}", folded_polynomial);
            let (polynomial_evaluations, polynomial_merkle_tree) = self.commit_polynomial(&folded_polynomial, &self.params.smooth_multiplicative_subgroup[round_index]);
        self.f.push(folded_polynomial);
            polynomial_commitment = polynomial_merkle_tree.root().unwrap();
            
            self.f_merkle_tree.push(polynomial_merkle_tree); // TODO optimize final round
            self.f_evaluation.push(polynomial_evaluations);
        }
        
        println!("Commitment: {:?}", polynomial_commitment);
        return polynomial_commitment;
    }

    fn execute_prover_query_round(&self, querying_challenge: usize) -> (Vec<Vec<F>>, Vec<MerkleProof<Sha256>>) {
        let mut coset_evaluation = Vec::new();
        let mut merkle_proof =  Vec::new();
        for index in 0..=self.params.num_rounds {
            let (coset_evaluation_i, merkle_proof_i) = self.open_polynomial(index, querying_challenge);
            coset_evaluation.push(coset_evaluation_i);
            merkle_proof.push(merkle_proof_i);
        }

        (coset_evaluation, merkle_proof)
    }
}



pub struct FriVerifier {
    params: Arc<FriParams>,
    f_merkle_root: Vec<[u8; 32]>,
    rng: StdRng,
    folding_challenge: Vec<F>,
    querying_challenge: Option<usize>,
}

impl FriVerifier {
    fn new(params: Arc<FriParams>) -> Self {
        let f_merkle_root = Vec::new();
        // Only cryptographically secure RNG for us
        let mut seed = [0u8; 32];
        OsRng.try_fill_bytes(&mut seed).unwrap();
        
        let rng = StdRng::from_seed(seed);
        let folding_challenge = Vec::new();
        let querying_challenge = None;
        FriVerifier {
            params,
            f_merkle_root,
            rng,
            folding_challenge,
            querying_challenge,
        }
    }

    fn interpolate(&self, values: &Vec<F>, coset_representative: F) -> DensePolynomial<F> {
        // TODO: rewrite codebase with built-in evaluation domain

        // Interpolate using a SFT (Slow Fourier Transform)
        // We are given the evaluations of a polynomial P on the values coset_representative * gen^j for 0 <= j < 2^eta.
        // Here gen_i generates smooth_multiplicative_subgroup[i] and gen generates homomorphism_kernel.
        // Let Q(x) = P(coset_representative * x). We have the values of Q on the 2^eta-th roots of unity and we can then
        // Reconstruct Q. Then we can find P via P(x) = Q(coset_representative^{-1} * x).

        let mut q_coefficients = Vec::new();
        for i in 0..self.params.two_to_the_eta {
            q_coefficients.push((0..self.params.two_to_the_eta).map(
                |j| self.params.homomorphism_kernel_generator.inverse().unwrap().pow(BigInt::<1>::from((i as u32) * (j as u32))) * values[j]                   
            ).sum::<F>() * (F::from(self.params.two_to_the_eta as u32).inverse().unwrap()));
        }

        let p = DensePolynomial::from_coefficients_vec(
    q_coefficients.iter().enumerate().map(
                |(j, coeff)| coset_representative.inverse().unwrap().pow(BigInt::<1>::from(j as u32)) * coeff
            ).collect()
        );
        p
    }

    fn execute_verifier_commit_round(&mut self, round_index: usize, merkle_root: [u8; 32]) -> Option<F> {
        println!("Verifier round: {}", round_index);
        self.f_merkle_root.push(merkle_root);
        if round_index < self.params.num_rounds {
            let folding_challenge = F::rand(&mut self.rng);
            println!("Verifier challenge: {:?}", folding_challenge);
            self.folding_challenge.push(folding_challenge);
            return Some(folding_challenge);
        } else {
            return None;
        }
    }

    fn execute_verifier_query_round_part_one(&mut self) -> usize {
        let querying_challenge = self.rng.gen_range(0..(2usize.pow(self.params.k[0])));
        self.querying_challenge = Some(querying_challenge);
        // for i in 0..self.params.num_rounds {
        //     querying_challenge_i = self.params.q.evaluate(&querying_challenge_i);
        //     self.querying_challenge.push(querying_challenge_i);

        //     for j in 0..self.params.two_to_the_eta {
        //         query_list.push((i, j));
        //     }
        // }
        querying_challenge
    }

    fn execute_verifier_query_round_part_two(&mut self, coset_evaluation: Vec<Vec<F>>, merkle_proof: Vec<MerkleProof<Sha256>>) -> bool {

        println!("Verifying merkle proofs...");
        println!("number of coset_evaluation vecs: {}", coset_evaluation.len());
        println!("number of merkle proofs: {}", merkle_proof.len());
        for index in 0..=self.params.num_rounds {
            // Verify the received merkle proofs.
            // Recall that the i-th smooth multiplicative subgroup has order 2^{k[i]}, while homomorphism_kernel has order 2^eta.
            let step_size = 2usize.pow(self.params.k[index] - self.params.eta);
            let leaf_hashes: Vec<[u8;32]> = coset_evaluation[index].iter().map(
                |x| value_to_merkle_leaf(x)
            ).collect();
            let exponents: Vec<usize> = (0..self.params.two_to_the_eta).map(
                |x| (self.querying_challenge.unwrap() + x * step_size) % (2usize.pow(self.params.k[index]))
            ).collect();
            println!("Verifier-computed exponents for polynomial {index}: {:?}", exponents);
            println!("Received evaluation claims for polynomial {index}: {:?}", coset_evaluation[index]);
            if !merkle_proof[index].verify(self.f_merkle_root[index], &exponents, &leaf_hashes, 2usize.pow(self.params.k[index])) {
                println!("The merkle proof in round {index} did not verify. Aborting...");
                return false;
            }

        }

        println!("Performing round consistency checks...");
        for index in 0..self.params.num_rounds {
            let p = self.interpolate(&coset_evaluation[index], self.params.generator[index].pow(BigInt::<1>::from(self.querying_challenge.unwrap() as u64)));
            if p.evaluate(&self.folding_challenge[index]) != coset_evaluation[index+1][0] {
                println!("The equation f^({})(s^({})) = p^({index})(x^({index})) did not hold. Aborting...", index+1, index+1);
            }
        }
        
        return true;
    }
}


pub struct FriProtocol {
    prover: FriProver,
    verifier: FriVerifier,
    polynomial: DensePolynomial<F>,
}

impl FriProtocol {
    fn new(polynomial: DensePolynomial<F>, eta: u32, rate_parameter: u32, degree_log_bound: u32, num_repetitions: usize) -> Self {
        let params = Arc::new(FriParams::new(eta, rate_parameter, degree_log_bound, num_repetitions));
        let prover = FriProver::new(params.clone(), polynomial.clone());
        let verifier = FriVerifier::new(params);
        FriProtocol {
            prover,
            verifier,
            polynomial,
        }
    }

    fn run(&mut self) {
        // PHASE 1: Commitment.

        let mut folding_challenge = None;

        // Prover accepts verifier challenge and generates commitment to the first folded polynomial.

        for round_index in 0..=self.prover.params.num_rounds {
            
            // During round 0, the folding challenge is None and the prover commits to the initial polynomial.
            // In subsequent rounds, the folding challenge is computed by the verifier at the end of the last round.
            let polynomial_commitment = self.prover.execute_prover_commit_round(round_index, folding_challenge);

            // In each round, the verifier records the polyomial commitment.
            // During the last round, the verifier outputs no verifier challenge (None). For each other round, it outputs a random challenge.
            folding_challenge = self.verifier.execute_verifier_commit_round(round_index, polynomial_commitment);

        }


        // PHASE 2: Verification.

        let exponent_offset = self.verifier.execute_verifier_query_round_part_one();
        let (coset_evaluation, merkle_proof) = self.prover.execute_prover_query_round(exponent_offset);
        let result = self.verifier.execute_verifier_query_round_part_two(coset_evaluation, merkle_proof);
        println!("FINAL VERIFIER OUTPUT:");
        if result {
            println!("ACCEPT");
        } else {
            println!("REJECT");
        }

    }
}


/// Deterministic function used to deterministically convert the value of a polynomial at a point
/// to a format suitable for insertion in a Merkle tree.
/// TODO make zero knowledge
fn value_to_merkle_leaf(value: &F ) -> [u8; 32] {
    Sha256::hash(&value.into_bigint().to_bytes_be())
}



fn main() {
    let eta = 2;
    let rate_parameter = 2;
    let degree_log_bound = 2;
    let num_repetitions = 3;

    let polynomial = DensePolynomial::<F>::from_coefficients_vec(
        (0..2_u32.pow(degree_log_bound)).map(|x| F::from(x)).collect()
    );
    let mut fri_protocol = FriProtocol::new(polynomial, eta, rate_parameter, degree_log_bound, num_repetitions);
    
    fri_protocol.run();
}

#[cfg(test)]
pub mod tests {
    use super::*;

    fn create_test_params() -> Arc<FriParams> {
        let eta = 2;
        let rate_parameter = 2;
        let degree_log_bound = 4;
        let num_repetitions = 3;
        let params = Arc::new(FriParams::new(eta, rate_parameter, degree_log_bound, num_repetitions));
        params
    }

    fn create_test_prover(polynomial: DensePolynomial<F>, params: Arc<FriParams>) -> FriProver {
        let prover = FriProver::new(params.clone(), polynomial.clone());
        prover
    }

    fn create_test_verifier(params: Arc<FriParams>) -> FriVerifier {
        let verifier = FriVerifier::new(params.clone());
        verifier
    }

    #[test]
    fn test_polynomial_folding(){
        
        let polynomial = DensePolynomial::<F>::from_coefficients_vec(vec![F::from(1), F::from(2), F::from(3), F::from(4)]);
        let params = create_test_params();
        let prover = create_test_prover(polynomial, params);
        let folding_challenge = F::from(3);
        let result = prover.fold_polynomial(&prover.f[0], folding_challenge);
        let expected = DensePolynomial::<F>::from_coefficients_vec(vec![F::from(7), F::from(15)]);
        println!("Result: {:?}", result);
        //println!("params: {:?}", prover.params);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_polynomial_commitment(){
        let polynomial = DensePolynomial::<F>::from_coefficients_vec(vec![F::from(1), F::from(2), F::from(3), F::from(4)]);
        let params = create_test_params();
        let prover = create_test_prover(polynomial, params);
        let (evaluations, merkle_tree) = prover.commit_polynomial(&prover.f[0], &prover.params.smooth_multiplicative_subgroup[0]);
        let proof = merkle_tree.proof(&[0]);
        let root = merkle_tree.root().expect("Merkle tree did not return root");
        let expected_value = &prover.f[0].evaluate(&F::from(1));
        let expected_leaf = value_to_merkle_leaf(expected_value);
        let unexpected_leaf = value_to_merkle_leaf(&(*expected_value + F::ONE));
        assert!(proof.verify(root, &[0], &[expected_leaf], merkle_tree.leaves_len()));
        assert!(! proof.verify(root, &[0], &[unexpected_leaf], merkle_tree.leaves_len()));
        assert_eq!(*expected_value, evaluations[0]);
    }

    #[test]
    fn test_interpolation(){
        let params = create_test_params();
        let verifier = create_test_verifier(params);

        let coefficients = vec![F::from(1), F::from(2), F::from(1), F::from(1)];
        let polynomial = DensePolynomial::from_coefficients_vec(coefficients);
        let coset_representative = F::from(3);

        let values = verifier.params.homomorphism_kernel.iter().map(
            |x| polynomial.evaluate(&(x * &coset_representative))
        ).collect();

        let reconstructed_polynomial = verifier.interpolate(&values, coset_representative);
        println!("Reconstructed polynomial: {:?}", reconstructed_polynomial);
        assert_eq!(polynomial, reconstructed_polynomial);
    }

    }
}



