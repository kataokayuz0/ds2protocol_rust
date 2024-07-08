use num_traits::ToPrimitive;
use num_traits::{One, Zero};
use rand::rngs::StdRng;
use rand::Rng;
use rand::SeedableRng;
use rand_distr::{Distribution, Normal, Uniform};
use sha2::{Digest, Sha256};
use std::fmt::Write;
use std::ops::{Add, Mul};
use std::sync::{Arc, Mutex};
use rug::ops::{Pow};
use rand_chacha::ChaCha20Rng;

const K: usize = 2;
const L: usize = 2;
const Q: i128 = 862214684689;
// const PRIMITIVE_ROOT: i128 = 79; //原始根
const N: usize = 1024;

fn main() {

    // Describe only functions related to the verification process
    // Perform the verification process by using the Ready_verification function and the each party_openck function
    let ver_w = ready_verification(
        &a_bar,
        derived_challenge,
        &pk_copy,
        &kappa_usize,
        &Q,
        &sign_zn,
        &com,
        &message,
        &trapl,
        &trapw,
        &t_sum,
    );
    eachparty_verification(
        &sign_zn,
        &com,
        &sign_rn,
        &ver_w,
        &ahat,
        large_b,
        party_number,
    );

}

fn ready_verification(
    a_bar: &Vec<Vec<Polynomial>>,
    challenge: &Polynomial,
    pk: &(Vec<Polynomial>, Vec<Polynomial>),
    kappa: &usize,
    q: &i128,
    sign_zn: &Vec<Polynomial>,
    com: &Vec<Vec<Vec<Polynomial>>>,
    message: &str,
    trapl: &usize,
    trapw: &usize,
    t_sum: &Vec<Polynomial>,
) -> Vec<Polynomial> {

    // Calculation of commitment_key using cgen as H3 function
    let ready_ck = c_gen(message, &pk, Q, trapl, trapw);

    // Calculation of challenge
    let ready_derived_challenge = h0(&com, message, &pk, N, kappa, &Q);

    // Multiplication of a_bar and sign_zn
    let ready_w_left: Vec<Polynomial> = multiply_polynomial_matrix_with_vector(a_bar, sign_zn, q);

    // Multiplication of hallenge and t_sum
    let recon_wn_right: Vec<Polynomial> = t_sum
        .iter()
        .map(|tsum_poly| {
            let mut product = challenge.clone().mul_ntt(tsum_poly);
            product
        })
        .collect();

    let ver_w: Vec<Polynomial> = ready_w_left
    .iter()
    .zip(recon_wn_right.iter())
    .map(|(left_poly, right_poly)| {
        left_poly.sub_ref(right_poly)
    })
    .collect();

    ver_w
}

// CGen function
fn c_gen(message: &str, pk: &(Vec<Polynomial>, Vec<Polynomial>), q: i128, trapl: &usize, trapw: &usize) -> Vec<Vec<Polynomial>> {
    // Initialize random number generator by calculating hash value from message and public key
    let mut hasher = Sha256::new();
    hasher.update(message.as_bytes());
    for poly in &pk.0 {
        hasher.update(poly.to_bytes()); // Polynomial byte representation
    }
    for poly in &pk.1 {
        hasher.update(poly.to_bytes()); 
    }
    let result = hasher.finalize();
    let seed = u64::from_ne_bytes(result[0..8].try_into().unwrap());
    let mut rng = ChaCha20Rng::seed_from_u64(seed);

    // Generate reversible 1*1 matrix
    let ahat1_1 = generate_invertible_matrix(&mut rng, q);
    let mut ahat1_j = generate_random_matrix(&mut rng,1, trapl + 2 * trapw - 1, q, 1)[0].clone();

    let mut first_row = vec![ahat1_1[0][0].clone()];
    first_row.append(&mut ahat1_j);

    let list1 = vec![
        Polynomial::new(vec![0], q),
        Polynomial::new(vec![1], q),
    ];
    let mut ahat2_j = generate_random_matrix(&mut rng,1, trapl + 2 * trapw - 1, q, 1)[0].clone();

    let mut second_row = list1;
    second_row.append(&mut ahat2_j);

    vec![first_row, second_row]
}

// Function to generate polynomials based on Gaussian samples (polynomials in ahat matrix)
fn gaussian_sample_polynomial<R: Rng>(
    rng: &mut R,
    q: i128,
) -> Polynomial {
    let coeffs: Vec<i128> = (0..N)
        .map(|_| {
            let sample: i128 = rng.gen_range(-(q as i128 / 2)..=(q as i128 / 2));
            (sample + q) % q // qで剰余を取る
        })
        .collect();

    Polynomial::new(coeffs, q)
}

// Function to generate kxl random polynomial matrices and store them in a list with the number of party_numbers
fn generate_random_matrix<R: Rng>(
    rng: &mut R,
    k: usize,
    l: usize,
    q: i128,
    party_number: usize,
) -> Vec<Vec<Polynomial>> {
    let mut matrices: Vec<Vec<Polynomial>> = Vec::with_capacity(party_number);
    for _ in 0..party_number {
        let matrix: Vec<Polynomial> = (0..k * l)
            .map(|_| gaussian_sample_polynomial(rng, q))
            .collect();
        matrices.push(matrix);
    }
    matrices
}

// Function to return an invertible 1*1 matrix
fn generate_invertible_matrix<R: Rng>(
    rng: &mut R,
    q: i128,
) -> Vec<Vec<Polynomial>> {
    loop {
        let ahat1_1: Vec<Vec<Polynomial>> = vec![vec![gaussian_sample_polynomial(rng, q)]];
        // For 1*1 matrices, we assume here that the polynomial is "invertible" by checking that it is non-zero
        if !ahat1_1[0][0].coeffs[0].is_zero() {
            return ahat1_1;
        }
    }
}

// Random oracle h0 function
fn h0(
    com: &Vec<Vec<Vec<Polynomial>>>,
    message: &str,
    pk: &(Vec<Polynomial>, Vec<Polynomial>),
    n: usize,
    kappa: &usize,
    q: &i128,
) -> Polynomial {
    let mut combined = String::new();
    write!(&mut combined, "{}", message).unwrap();

    // Adjusting to handle three-dimensional vector of polynomials
    for poly_group in com {
        for poly_list in poly_group {
            for poly in poly_list {
                write!(&mut combined, "{}", poly.to_string()).unwrap();
            }
        }
    }

    for poly in &pk.0 {
        write!(&mut combined, "{}", poly.to_string()).unwrap();
    }

    for poly in &pk.1 {
        write!(&mut combined, "{}", poly.to_string()).unwrap();
    }

    let mut hasher = Sha256::new();
    hasher.update(combined.as_bytes());
    let hash_result = hasher.finalize();

    let seed = u64::from_le_bytes([
        hash_result[0],
        hash_result[1],
        hash_result[2],
        hash_result[3],
        hash_result[4],
        hash_result[5],
        hash_result[6],
        hash_result[7],
    ]);

    let mut rng = StdRng::seed_from_u64(seed);
    let mut positions = Vec::new();

    while &positions.len() < kappa {
        let pos = rng.gen_range(0..n);
        if !positions.contains(&pos) {
            positions.push(pos);
        }
    }

    positions.sort(); // Sort positions for consistency

    let mut coeffs = vec![0; n];
    for &pos in &positions {
        coeffs[pos] = if rng.gen() { 1 } else { q - 1 };
    }

    Polynomial::new(coeffs, q.clone())
}

// Polynomial matrix and vector multiplication functions
fn multiply_polynomial_matrix_with_vector(
    a_bar: &Vec<Vec<Polynomial>>,
    vector: &Vec<Polynomial>,
    q: &i128,
) -> Vec<Polynomial> {
    let mut result = Vec::new();
    for a_bar_row in a_bar.iter() {
        let mut sum_poly = Polynomial::new(vec![0], q.clone());
        for (a_poly, v_poly) in a_bar_row.iter().zip(vector.iter()) {
            let product = a_poly.mul(v_poly.clone());
            sum_poly = sum_poly.add(product);
        }
        result.push(sum_poly);
    }
    result
}

// Functions to validate each party
fn eachparty_verification(
    sign_zn: &Vec<Polynomial>,
    com: &Vec<Vec<Vec<Polynomial>>>,
    sign_rn: &Vec<Polynomial>,
    ver_w: &Vec<Polynomial>,
    ahat: &Vec<Vec<Polynomial>>,
    b: f64,
    party_number: usize,
) {
    // Calculate the norm of sign_zn and bound value bn
    let zn_norm = calculate_norms_for_polynomial_vector(sign_zn);
    let bn = (party_number as f64).sqrt() * b;

    let mut verification_failed = false;

    for i in 0..party_number {
        if zn_norm[0] > bn || eachparty_openck(sign_rn, ver_w, com, ahat, bn, K).is_err() {
            println!("Verification is invalid for party {}", i);
            verification_failed = true;
            break;
        }
    }

    if !verification_failed {
        println!("All verifications are valid.");
    }
}

// Function to compute the norm of each polynomial for data in Vec<Polynomial> format
fn calculate_norms_for_polynomial_vector(polynomials: &Vec<Polynomial>) -> Vec<f64> {
    polynomials
        .iter()
        .map(|poly| {
            let mod_val_f64 = poly.mod_val.to_f64().unwrap_or(0.0); 
            let half_mod = mod_val_f64 / 2.0;

            poly.coeffs
                .iter()
                .fold(0.0, |acc, &coeff| {
                    let coeff_f64 = coeff.to_f64().unwrap_or(0.0); 
                    let adjusted_coeff = if coeff_f64 > half_mod {
                        coeff_f64 - mod_val_f64 
                    } else {
                        coeff_f64
                    };
                    acc + adjusted_coeff.powi(2) 
                })
                .sqrt() // Calculate the square root of the sum of squares to obtain the norm
        })
        .collect()
}

// Verify commitment for each party
fn eachparty_openck(
    sign_rn: &Vec<Polynomial>,
    ver_w: &Vec<Polynomial>,
    com: &Vec<Vec<Vec<Polynomial>>>,
    ahat: &Vec<Vec<Polynomial>>, // Ahatを加える
    bn: f64,
    k: usize,
) -> Result<(), String> {
    let sign_rn_norms = calculate_norms_for_polynomial_vector(sign_rn);

    for j in 0..(k - 1) {
        let each_openck_fleft = multiply_ahat_with_sampled_matrix(ahat, &sign_rn[0]);
        let temp_ver_w = &ver_w[j];
        let cols = 1;
        let temp_matrix_zero = vec![Polynomial::new(vec![0], ahat[0][0].mod_val.clone()); cols];
        let each_openck_zero_x = ver_combine_matrices_vertically(&temp_matrix_zero, temp_ver_w);
        let each_openck_result = add_polynomial_matrices(&each_openck_fleft, &each_openck_zero_x);

        // com[j] と each_openck_result を比較
        if sign_rn_norms[0] <= bn && com[j] == each_openck_result {
            continue;
        } else {
            println!("eachparty_openck is aborted");
            return Err("abort".to_string());
        }
    }
    Ok(())
}

fn multiply_ahat_with_sampled_matrix(
    ahat: &Vec<Vec<Polynomial>>,
    sampled_poly: &Polynomial,
) -> Vec<Vec<Polynomial>> {
    let mut result = Vec::new();
    for ahat_row in ahat.iter() {
        let mut sum_poly = Polynomial::new(vec![0], sampled_poly.mod_val.clone());

        // Multiply each polynomial in ahat_row by each coefficient in sampled_poly and add
        for (ahat_poly, coeff) in ahat_row.iter().zip(sampled_poly.coeffs.iter()) {
            let mut product_poly = ahat_poly.clone();
            // Generate a new polynomial by multiplying each coefficient of ahat_poly by the coefficient of sampled_poly
            for p in product_poly.coeffs.iter_mut() {
                *p *= coeff;
                *p %= &sampled_poly.mod_val;
            }
            sum_poly = sum_poly.add_ref(&product_poly); 
        }
        result.push(vec![sum_poly]); 
    }
    result
}

// Function to combine each element correctly
fn ver_combine_matrices_vertically(
    matrix_zero: &Vec<Polynomial>,
    reconted_wj: &Polynomial,
) -> Vec<Vec<Polynomial>> {
    let mut combined_matrix = Vec::new();

    // 0の多項式を独立したベクトルとして追加
    for zero_poly in matrix_zero.iter() {
        combined_matrix.push(vec![zero_poly.clone()]);
    }

    // reconted_wjを別のベクトルとして追加
    combined_matrix.push(vec![reconted_wj.clone()]);

    combined_matrix
}

// Function to add two matrices of type Vec<Vec<Polynomial>>
fn add_polynomial_matrices(
    matrix1: &Vec<Vec<Polynomial>>,
    matrix2: &Vec<Vec<Polynomial>>,
) -> Vec<Vec<Polynomial>> {
    matrix1
        .iter()
        .zip(matrix2.iter())
        .map(|(row1, row2)| {
            row1.iter()
                .zip(row2.iter())
                .map(|(poly1, poly2)| {
                    poly1.add_ref(&poly2)
                })
                .collect()
        })
        .collect()
}
