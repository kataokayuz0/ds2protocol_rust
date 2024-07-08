use num_traits::ToPrimitive;
use rand::rngs::ThreadRng;
use rand::thread_rng;
use rand::Rng;
use rand_distr::{Distribution, Normal, Uniform};
use sha2::{Digest, Sha256};
use std::sync::{Arc, Mutex};
use rug::{Assign, Float};
use rug::ops::{Pow};

const K: usize = 2;
const L: usize = 2;
const Q: i128 = 862214684689;
// const PRIMITIVE_ROOT: i128 = 79; // primitive root of Q
const N: usize = 1024;

fn main() {
    // Definition of various variables
    let party_number: usize = 1000;
    let f64_party_number = party_number as f64;
    let eta: i128 = 5;
    let eta_f64: f64 = eta as f64;

    let message: &str = "example_message";

    let alpha: f64 = 11.0 * f64_party_number * 10.0;
    let kappa_usize = 5;
    let gamma: f64 = 1.1;
    let t: f64 = 12.0;
    let n: f64 = N as f64;
    let l: f64 = L as f64;
    let k: f64 = K as f64;
    let kappa: f64 = kappa_usize as f64;

    let large_t = kappa * eta_f64 * (n * (l + k)).sqrt();
    let sigma = &alpha * &large_t;
    let large_b = gamma * sigma * (n * (l + k)).sqrt();

    let m_f64 = ((t / alpha) + (1.0 / (2.0 * alpha.powi(2)))).exp();
    let mn = m_f64.powf(f64_party_number); // The expected number of restarts until all n parties proceed simultaneously

    let trapl = Q.to_f64().unwrap().log(20.0).ceil() as usize;
    let trapw = Q.to_f64().unwrap().log(20.0).ceil() as usize;
    // Match the standard deviation format to the sampler
    let s = sigma.clone();
    // let s = &alpha * &large_t * (2.0 * std::f64::consts::PI).sqrt();
    let sampler = GaussianSampler::new(sigma);

    // let mut last_rejec_zn_result: Option<Vec<Vec<Polynomial>>> = None;
    // let mut last_derived_challenge: Option<Polynomial> = None;
    // let mut sampled_rn: Vec<Vec<Polynomial>> = Vec::new();
    // let mut comn_per_party: Vec<Vec<Polynomial>> = Vec::new();
    // let mut ahat: Vec<Vec<Polynomial>> = Vec::new();
    // let mut wn: Vec<Vec<Polynomial>> = Vec::new();
    // let mut com: Vec<Polynomial> = Vec::new();
    // let mut computed_zn: Vec<Vec<Polynomial>> = Vec::new();
    // let mut csn: Vec<Vec<Polynomial>> = Vec::new();
    // let mut sample_yn: Vec<Vec<Polynomial>> = Vec::new();

    // Protocol DS2.Sign_n(sid, sk_n, pk, myu)
    loop {
        sample_yn = sampleyn(L, K, &sampler, Q, party_number);
        // wn = computewn(&a_bar, &sample_yn, &Q);
        sampled_rn = samplern(party_number, trapl, trapw, &sampler, Q);

        // Generate commitment key (ck=ahat) using cgen as H3 function
        // ahat = c_gen(message, &pk, Q, &trapl, &trapw);

        // let result = commitck(&wn, &sampled_rn, &ahat, party_number);
        // let (zero, comn) = result;
        // comn_per_party = comn;

        // com = setcom(comn_per_party.clone(), K);
        // let derived_challenge = h0(&com, message, &pk_copy, N, &kappa_usize, &Q);
        (computed_zn, csn) = compute_zn_ntt(&derived_challenge, &sn, &sample_yn);

        match rejection_sample(&csn, &computed_zn, s, m_f64) {
            Ok(rejec_zn_result) => {
                println!("Accepted signature shares");
                last_rejec_zn_result = Some(rejec_zn_result);
                last_derived_challenge = Some(derived_challenge.clone());
                break;
            }
            Err(_) => {
                println!("Restarting sampling...");
                continue;
            }
        }
    }

    if let (Some(rejec_zn_result), Some(derived_challenge)) =
        (&last_rejec_zn_result, &last_derived_challenge)
    {
        // let reconted_wj = recon_wj(&a_bar, derived_challenge, &tn, &Q, &rejec_zn_result);
        if validate_zn(&rejec_zn_result, large_b) == "abort" {
            println!("protocol aborted by zn_value check.");
        // } else if validate_openck(
        //     &sampled_rn,
        //     &reconted_wj,
        //     &comn_per_party.clone(),
        //     large_b,
        //     &ahat,
        //     K,
        // ) == "abort"
        // {
        //     println!("protocol aborted by openck check.");
        } else {
            println!("Let's go!");
            let (sign_zn, sign_rn) = compute_signature(&rejec_zn_result, &sampled_rn);
        }    
    }        
}

// Structure for Gaussian sampling
struct GaussianSampler {
    normal: Normal<f64>,   // Using the standard normal distribution
    rng: Mutex<ThreadRng>, // Using a random number generator in a thread-safe manner
}

impl GaussianSampler {
    fn new(sigma: f64) -> Self {
        let normal = Normal::new(0.0, sigma).expect("Failed to create normal distribution.");
        let rng = Mutex::new(thread_rng());
        Self { normal, rng }
    }

    fn sample(&self) -> i128 {
        let mut rng = self.rng.lock().unwrap();
        let value = self.normal.sample(&mut *rng);
        let rounded_value = value.round() as i128; // Explicit type conversion from f64 to i128
        rounded_value
    }
}

// // Function to generate polynomials based on Gaussian samples (polynomials in ahat matrix)
// fn sample_polynomial_for_ahat<R: Rng>(
//     rng: &mut R,
//     q: i128,
// ) -> Polynomial {
//     let range = Uniform::new(-(q / 2), q / 2 + 1);
//     let coeffs: Vec<i128> = (0..N)
//         .map(|_| {
//             let sample = range.sample(rng);
//             (sample + q) % q // qで剰余を取る
//         })
//         .collect();

//     Polynomial::new(coeffs, q)
// }

// Function to generate polynomials based on Gaussian samples (polynomials in yn, rn)
fn gaussian_sample_polynomial_for_yn_rn(sampler: &GaussianSampler, q: i128) -> Polynomial {
    let coeffs: Vec<i128> = (0..N)
        .map(|_| {
            let sample = sampler.sample() as i128; // Cast sampled integer to f64
            let signed_sample = if thread_rng().gen::<bool>() {
                q + sample
            } else {
                q - sample
            };
            signed_sample % q 
        })
        .collect();

    Polynomial::new(coeffs, q)
}

// // Function to generate kxl random polynomial matrices and store them in a list with the number of party_numbers
// fn generate_random_matrix<R: Rng>(
//     rng: &mut R,
//     k: usize,
//     l: usize,
//     q: i128,
//     party_number: usize,
// ) -> Vec<Vec<Polynomial>> {
//     let mut matrices: Vec<Vec<Polynomial>> = Vec::with_capacity(party_number);
//     for _ in 0..party_number {
//         let matrix: Vec<Polynomial> = (0..k * l)
//             .map(|_| sample_polynomial_for_ahat(rng, q))
//             .collect();
//         matrices.push(matrix);
//     }
//     matrices
// }

// // Function to return an invertible 1*1 matrix
// fn generate_invertible_matrix<R: Rng>(
//     rng: &mut R,
//     q: i128,
// ) -> Vec<Vec<Polynomial>> {
//     loop {
//         let ahat1_1: Vec<Vec<Polynomial>> = vec![vec![sample_polynomial_for_ahat(rng, q)]];
//         // For 1*1 matrices, we assume here that the polynomial is "invertible" by checking that it is non-zero
//         if !ahat1_1[0][0].coeffs[0].is_zero() {
//             return ahat1_1;
//         }
//     }
// }

// Multiply a polynomial matrix by a vector of polynomials
fn multiply_polynomial_matrix_vector(
    matrix: &[Vec<Polynomial>],
    vector: &[Vec<Polynomial>],
    mod_value: &i128,
) -> Vec<Vec<Polynomial>> {
    let num_columns = vector.len();
    let mut result = Vec::with_capacity(num_columns);

    for column in 0..num_columns {
        let mut column_result = Vec::new();

        for matrix_row in matrix.iter() {
            let mut result_poly = Polynomial::new(vec![0; matrix_row[0].coeffs.len()], *mod_value);

            // element-by-element multiplication and addition of matrix rows and specific columns of vector
            for (matrix_poly, vector_poly) in matrix_row.iter().zip(&vector[column]) {
                let product = matrix_poly.mul_ntt(vector_poly);
                result_poly = result_poly.add_ref(&product);
            }

            column_result.push(result_poly);
        }

        result.push(column_result);
    }

    result
}

// // Generate a random oracle commitment for a vector of polynomials
// fn random_oracle_commitment_polynomials(
//     polynomials: &Vec<Polynomial>,
//     party_number: u128,
// ) -> String {
//     let mut combined = String::new();
//     for poly in polynomials {
//         write!(&mut combined, "{}", poly.to_string()).expect("Failed to write to string");
//     }
//     write!(&mut combined, "{}", party_number).expect("Failed to write to string");
//     let mut hasher = Sha256::new();
//     hasher.update(combined.as_bytes());
//     let hash_result = hasher.finalize();
//     format!("{:x}", hash_result)
// }

//a. sample yn and compute wn
fn sampleyn(
    l: usize,
    k: usize,
    sampler: &GaussianSampler,
    q: i128,
    party_number: usize,
) -> Vec<Vec<Polynomial>> {
    (0..party_number)
        .map(|_| {
            (0..(l + k))
                .map(|_| gaussian_sample_polynomial_for_yn_rn(&sampler, q))
                .collect()
        })
        .collect()
}

// performs multiplication of a_bar and sample_yn and returns the result as a vector of k * 1
fn computewn(
    a_bar: &Vec<Vec<Polynomial>>,
    sample_yn: &Vec<Vec<Polynomial>>,
    q: &i128,
) -> Vec<Vec<Polynomial>> {
    multiply_polynomial_matrix_vector(a_bar, sample_yn, q)
}

//b. compute comn with rn
// Function to generate Polynomial vectors
fn samplern(
    party_number: usize,
    trapl: usize,
    trapw: usize,
    sampler: &GaussianSampler,
    q: i128,
) -> Vec<Vec<Polynomial>> {
    (0..party_number)
        .map(|_| {
            (0..(trapl + 2 * trapw))  // (trapl + 2trapw) の長さのベクトルを生成
                .map(|_| gaussian_sample_polynomial_for_yn_rn(sampler, q))
                .collect::<Vec<Polynomial>>()
        })
        .collect()
}

// // CGen function
// fn c_gen(message: &str, pk: &(Vec<Polynomial>, Vec<Polynomial>), q: i128, trapl: &usize, trapw: &usize) -> Vec<Vec<Polynomial>> {
//     // Initialize random number generator by calculating hash value from message and public key
//     let mut hasher = Sha256::new();
//     hasher.update(message.as_bytes());
//     for poly in &pk.0 {
//         hasher.update(poly.to_bytes()); // Polynomial byte representation
//     }
//     for poly in &pk.1 {
//         hasher.update(poly.to_bytes()); 
//     }
//     let result = hasher.finalize();
//     let seed = u64::from_ne_bytes(result[0..8].try_into().unwrap());
//     let mut rng = ChaCha20Rng::seed_from_u64(seed);

//     // Generate reversible 1*1 matrix
//     let ahat1_1 = generate_invertible_matrix(&mut rng, q);
//     let mut ahat1_j = generate_random_matrix(&mut rng,1, trapl + 2 * trapw - 1, q, 1)[0].clone();

//     let mut first_row = vec![ahat1_1[0][0].clone()];
//     first_row.append(&mut ahat1_j);

//     let list1 = vec![
//         Polynomial::new(vec![0], q),
//         Polynomial::new(vec![1], q),
//     ];
//     let mut ahat2_j = generate_random_matrix(&mut rng,1, trapl + 2 * trapw - 2, q, 1)[0].clone();

//     let mut second_row = list1;
//     second_row.append(&mut ahat2_j);

//     vec![first_row, second_row]
// }

// // Function to calculate commitment
// fn commitck(
//     flat_wn: &Vec<Vec<Polynomial>>,
//     sampled_rn: &Vec<Vec<Polynomial>>,
//     ahat: &Vec<Vec<Polynomial>>,
//     party_number: usize,
// ) -> (Vec<Vec<Polynomial>>, Vec<Vec<Vec<Polynomial>>>) {
//     let mut comn_per_party = vec![Vec::new(); party_number]; 

//     for (p, (temp_wn, sampled_rn_poly)) in flat_wn.iter().zip(sampled_rn.iter()).enumerate() {

//         for (poly, sampled_poly) in temp_wn.iter().zip(sampled_rn_poly.iter()) {
//             let fleft = multiply_ahat_with_sampled_matrix(ahat, &sampled_poly.clone());
//             let fright_poly_matrix = combine_matrices_vertically(
//                 &vec![Polynomial::new(vec![0], ahat[0][0].mod_val.clone())],
//                 &vec![poly.clone()],
//             );

//             let formatted_fleft = format_openck_fleft(fleft);
//             let f = add_formatted_matrices(&formatted_fleft, &fright_poly_matrix);

//             let party_index = p % party_number;
//             comn_per_party[party_index].extend(f);
//         }
//     }

//     let matrix_zero = vec![vec![Polynomial::new(vec![0], ahat[0][0].mod_val.clone())]];
//     return (matrix_zero, comn_per_party);
// }

// fn multiply_ahat_with_sampled_matrix(
//     ahat: &Vec<Vec<Polynomial>>,
//     sampled_poly: &Polynomial,
// ) -> Vec<Vec<Polynomial>> {
//     let mut result = Vec::new();
//     for ahat_row in ahat.iter() {
//         let mut sum_poly = Polynomial::new(vec![0], sampled_poly.mod_val.clone());

//         // Multiply each polynomial in ahat_row by each coefficient in sampled_poly and add
//         for (ahat_poly, coeff) in ahat_row.iter().zip(sampled_poly.coeffs.iter()) {
//             let mut product_poly = ahat_poly.clone();
//             // Generate a new polynomial by multiplying each coefficient of ahat_poly by the coefficient of sampled_poly
//             for p in product_poly.coeffs.iter_mut() {
//                 *p *= coeff;
//                 *p %= &sampled_poly.mod_val;
//             }
//             sum_poly = sum_poly.add_ref(&product_poly); 
//         }
//         result.push(vec![sum_poly]); 
//     }
//     result
// }

// fn combine_matrices_vertically(
//     matrix_zero: &Vec<Polynomial>,
//     reconted_wj: &Vec<Polynomial>,
// ) -> Vec<Vec<Vec<Polynomial>>> {
//     let mut combined_matrix = Vec::new();

//     for index in 0..matrix_zero.len() {
//         let mut combined_row = Vec::new();
//         combined_row.push(vec![matrix_zero[index].clone()]);
//         combined_row.push(vec![reconted_wj[index].clone()]);
//         combined_matrix.push(combined_row);
//     }

//     combined_matrix
// }

// // Change fleft format to avoid extra nesting
// fn format_openck_fleft(openck_fleft: Vec<Vec<Polynomial>>) -> Vec<Vec<Vec<Polynomial>>> {
//     vec![openck_fleft]
// }

// // Fix function that adds two multilayer matrices and returns a flat matrix 
// fn add_formatted_matrices(
//     matrix1: &Vec<Vec<Vec<Polynomial>>>,
//     matrix2: &Vec<Vec<Vec<Polynomial>>>,
// ) -> Vec<Vec<Polynomial>> {
//     let mut combined_matrix = Vec::new();

//     for (rows1, rows2) in matrix1.iter().zip(matrix2.iter()) {
//         for (row1, row2) in rows1.iter().zip(rows2.iter()) {
//             let mut combined_row = Vec::new();
//             for (poly1, poly2) in row1.iter().zip(row2.iter()) {
//                 combined_row.push(poly1.add_ref(poly2));
//             }
//             combined_matrix.push(combined_row);
//         }
//     }

//     combined_matrix
// }

// // a. set com
// // Function to calculate total commitment from comn_per_party
// fn setcom(comn_per_party: Vec<Vec<Vec<Polynomial>>>, k: usize) -> Vec<Vec<Vec<Polynomial>>> {
//     if comn_per_party.is_empty() {
//         return Vec::new();
//     }

//     let num_rows = comn_per_party[0].len();
//     let num_cols = if num_rows > 0 {
//         comn_per_party[0][0].len()
//     } else {
//         0
//     };

//     // Changed initialization method to store results in a two-dimensional list instead of a one-dimensional list
//     let mut grouped_results = vec![Vec::new(); num_rows / k]; // k個ずつグループ化するための二次元ベクター

//     // Create a flat list to store temporary results
//     let mut temp_results = vec![vec![Polynomial::new(vec![0], Q); num_cols]; num_rows];

//     // Adds up all the elements of the input data
//     for party_coms in comn_per_party {
//         for (i, row_coms) in party_coms.iter().enumerate() {
//             for (j, com) in row_coms.iter().enumerate() {
//                 temp_results[i][j] = temp_results[i][j].add_ref(com);
//             }
//         }
//     }

//     // Divide one-dimensional results into two-dimensional groups
//     for (i, result) in temp_results.iter().enumerate() {
//         let group_index = i / k; 
//         grouped_results[group_index].push(result.clone()); 
//     }

//     grouped_results
// }

// // b. derive challenge
// // Random oracle h0 function
// fn h0(
//     com: &Vec<Vec<Vec<Polynomial>>>,
//     message: &str,
//     pk: &(Vec<Polynomial>, Vec<Polynomial>),
//     n: usize,
//     kappa: &usize,
//     q: &i128,
// ) -> Polynomial {
//     let mut combined = String::new();
//     write!(&mut combined, "{}", message).unwrap();

//     // Adjusting to handle three-dimensional vector of polynomials
//     for poly_group in com {
//         for poly_list in poly_group {
//             for poly in poly_list {
//                 write!(&mut combined, "{}", poly.to_string()).unwrap();
//             }
//         }
//     }

//     for poly in &pk.0 {
//         write!(&mut combined, "{}", poly.to_string()).unwrap();
//     }

//     for poly in &pk.1 {
//         write!(&mut combined, "{}", poly.to_string()).unwrap();
//     }

//     let mut hasher = Sha256::new();
//     hasher.update(combined.as_bytes());
//     let hash_result = hasher.finalize();

//     let seed = u64::from_le_bytes([
//         hash_result[0],
//         hash_result[1],
//         hash_result[2],
//         hash_result[3],
//         hash_result[4],
//         hash_result[5],
//         hash_result[6],
//         hash_result[7],
//     ]);

//     let mut rng = StdRng::seed_from_u64(seed);
//     let mut positions = Vec::new();

//     while &positions.len() < kappa {
//         let pos = rng.gen_range(0..n);
//         if !positions.contains(&pos) {
//             positions.push(pos);
//         }
//     }

//     positions.sort(); // Sort positions for consistency

//     let mut coeffs = vec![0; n];
//     for &pos in &positions {
//         coeffs[pos] = if rng.gen() { 1 } else { q - 1 };
//     }

//     Polynomial::new(coeffs, q.clone())
// }

// c. Computes a signature share using element-wise multiplication
fn compute_zn_ntt(
    derived_challenge: &Polynomial,
    sn: &Vec<Vec<Polynomial>>,
    sample_yn: &Vec<Vec<Polynomial>>,
) -> (Vec<Vec<Polynomial>>, Vec<Vec<Polynomial>>) {
    let csn: Vec<Vec<Polynomial>> = sn
        .iter()
        .map(|poly_vec| {
            poly_vec
                .iter()
                .map(|poly| {
                    let mut product = derived_challenge.clone().mul_ntt(&poly.clone());
                    product
                })
                .collect()
        })
        .collect();

    let computed_zn: Vec<Vec<Polynomial>> = csn
        .iter()
        .zip(sample_yn.iter())
        .map(|(csn_row, sample_yn_row)| {
            csn_row
                .iter()
                .zip(sample_yn_row)
                .map(|(csn_elem, sample_yn_elem)| {
                    let sum = csn_elem.add_ref(sample_yn_elem); // 加算
                    sum
                })
                .collect()
        })
        .collect();

    (computed_zn, csn)
}

//d. Run the rejection sampling
fn rejection_sample(
    csn_list: &Vec<Vec<Polynomial>>,
    zn_list: &Vec<Vec<Polynomial>>,
    s: f64,
    m: f64,
) -> Result<Vec<Vec<Polynomial>>, &'static str> {
    let mut rejec_zn_party_result: Vec<Vec<Polynomial>>  = Vec::new();
    let mut rohs_zns = Vec::new();
    let mut rohcsn_s_zns = Vec::new();
    let mut sum_rohs_zn = 0.0;
    let mut sum_rohcsn_s_zn = 0.0;

    // Do the computation inside exp first, since the values will be very small
    // Loop over outer vectors (list per party)
    for (csn_party, zn_party) in csn_list.iter().zip(zn_list.iter()) {

        // Create an overall vector for each party
        let csn_combined: Vec<f64> = csn_party.iter().flat_map(|poly| polynomial_to_f64_vec(poly)).collect();
        let zn_combined: Vec<f64> = zn_party.iter().flat_map(|poly| polynomial_to_f64_vec(poly)).collect();

        // Calculate norm for each party
        let (rohs_zn, rohcsn_s_zn) = calculate_sums_for_poly(&csn_combined, &zn_combined, s);
        rohs_zns.push(rohs_zn);
        rohcsn_s_zns.push(rohcsn_s_zn);
        sum_rohs_zn += rohs_zn;
        sum_rohcsn_s_zn += rohcsn_s_zn;

    }

    for ((rohs_zn, rohcsn_s_zn), zn_list) in rohs_zns.iter().zip(rohcsn_s_zns.iter()).zip(zn_list.iter()) {
        // Perform rejection sampling for each party
        let ratio = ((rohs_zn / sum_rohs_zn).exp()) / (m * ((rohcsn_s_zn / sum_rohcsn_s_zn).exp()));
        println!("Ratio: {}", ratio);

        // Choose the smaller of the ratio and 1
        let acceptance_probability = ratio.min(1.0);
        let random_probability: f64 = rand::random();

        // Use random probabilities to accept or reject samples
        if random_probability <= acceptance_probability {
            rejec_zn_party_result.push(zn_list.clone());
        } else {
            return Err("restart");
        }
    }
    Ok(rejec_zn_party_result)
}

// Ratio computation function for a single polynomial with arbitrary precision
fn calculate_sums_for_poly(csn: &Vec<f64>, zn: &Vec<f64>, s: f64) -> (f64, f64) {
    let precision = 50;
    let pi = Float::with_val(precision, std::f64::consts::PI);
    let s = Float::with_val(precision, s);

    let zn_norm = Float::with_val(precision, calculate_norm(zn));
    let csn_minus_zn = sub_ref_f64(zn, csn);
    let csn_norm = Float::with_val(precision, calculate_norm(&csn_minus_zn));

    let zn_norm_squared: Float = zn_norm.clone().pow(2);
    // Transformation process to match the type of Gaussian distribution
    let sigma_translate: Float = s * (Float::with_val(precision, 2.0) * pi).sqrt();
    let s_squared: Float = sigma_translate.clone().pow(2); 
    let csn_norm_squared: Float = csn_norm.pow(2); 

    let rohs_zn = -(zn_norm_squared / (Float::with_val(precision, 2.0) * s_squared.clone()));
    let rohcsn_s_zn = -(csn_norm_squared / (Float::with_val(precision, 2.0)* s_squared.clone()));

    (rohs_zn.to_f64(), rohcsn_s_zn.to_f64())
}

// Function to convert a polynomial into a vector of f64
fn polynomial_to_f64_vec(poly: &Polynomial) -> Vec<f64> {
    let half_mod_val = poly.mod_val / 2;

    poly.coeffs
        .iter()
        .map(|&coeff| {
            let adjusted_coeff = if coeff > half_mod_val {
                // If the coefficient exceeds half of the modulus, it is interpreted as a negative value
                (coeff as i128 - poly.mod_val) as f64
            } else {
                // Otherwise, interpreted as positive value as is
                coeff as f64
            };
            adjusted_coeff
        })
        .collect()
}

// Function to compute the norm of a vector
fn calculate_norm(vec: &Vec<f64>) -> f64 {
    vec.iter().map(|&x| x * x).sum::<f64>().sqrt()
}

// Subtract between the elements of Vec<f64> and return the resulting Vec<f64>
fn sub_ref_f64(a: &Vec<f64>, b: &Vec<f64>) -> Vec<f64> {
    let max_len = std::cmp::max(a.len(), b.len());
    let mut result = vec![0.0; max_len];

    for i in 0..max_len {
        let a_val = *a.get(i).unwrap_or(&0.0); 
        let b_val = *b.get(i).unwrap_or(&0.0);
        result[i] = a_val - b_val;
    }

    result
}

// Validate the computed zn values
fn validate_zn(zn_result: &Vec<Vec<Polynomial>>, large_b: f64) -> String {
    for zn_party in zn_result {
        // Combine polynomial vectors of each party into one large vector
        let combined_coeffs: Vec<f64> = zn_party
            .iter()
            .flat_map(|poly| polynomial_to_f64_vec(poly))
            .collect();

        // Calculate norm of combined vectors
        let zn_norm = calculate_norm(&combined_coeffs);
        println!("Combined zn_norm: {}", zn_norm);
        println!("large_b: {}", large_b);

        // If norm is greater than large_b, process is aborted
        if zn_norm > large_b {
            return "abort".to_string();
        }
    }
    "continue".to_string()
}

// // Fixed the relevant part in the `recon_wj` function
// fn recon_wj(
//     a_bar: &Vec<Vec<Polynomial>>,
//     challenge: &Polynomial,
//     tn: &Vec<Vec<Polynomial>>,
//     q: &i128,
//     zn: &Vec<Vec<Polynomial>>,
// ) -> Vec<Vec<Polynomial>> {
//     let mut reconted_wj = Vec::new();

//     // Calculate challenge * tn and save it in the correct format
//     let recon_wn_rights: Vec<Vec<Polynomial>> = tn
//         .iter()
//         .map(|tn_row| {
//             tn_row
//                 .iter()
//                 .map(|tn_poly| {
//                     let mut product = challenge.clone().mul_ntt(&tn_poly.clone());
//                     product
//                 })
//                 .collect()
//         })
//         .collect();

//     // Multiply a_bar by zn and store the result
//     let addition_result = multiply_polynomial_matrix_vector(a_bar, zn, q);

//     // Subtract recon_wn_rights from addition_result as final result
//     for (addition_row, recon_wn_right_row) in addition_result.iter().zip(recon_wn_rights.iter()) {
//         let reconted_row: Vec<Polynomial> = addition_row
//             .iter()
//             .zip(recon_wn_right_row)
//             .map(|(addition_poly, recon_wn_right_poly)| {
//                 let mut result = addition_poly.clone().sub(recon_wn_right_poly.clone());
//                 result
//             })
//             .collect();
//         reconted_wj.push(reconted_row);
//     }

//     reconted_wj
// }

// fn validate_openck(
//     sampled_rn: &Vec<Vec<Polynomial>>,
//     reconted_wj: &Vec<Vec<Polynomial>>,
//     comn_per_party: &Vec<Vec<Vec<Polynomial>>>,
//     large_b: f64,
//     ahat: &Vec<Vec<Polynomial>>,
//     k: usize,
// ) -> String {
//     let mut poly_index = 0;

//     for (j, (temp_reconted_wj, temp_sampled_rn)) in reconted_wj.iter().zip(sampled_rn.iter()).enumerate() {

//         for (_poly, sampled_poly) in temp_reconted_wj.iter().zip(temp_sampled_rn.iter()) {
//             let openck_fleft = multiply_ahat_with_sampled_matrix(ahat, &sampled_poly.clone());
//             let openck_zero_x = combine_matrices_vertically(
//                 &vec![Polynomial::new(vec![0], ahat[0][0].mod_val.clone())],
//                 &vec![_poly.clone()],
//             );
//             let formatted_openck_fleft = format_openck_fleft(openck_fleft);
//             let openck_result = add_formatted_matrices(&formatted_openck_fleft, &openck_zero_x);

//             // Use poly_index to calculate the correct comn_per_party segment
//             let group_index = poly_index / k; // Calculate the index of the polynomial group in each sublist
//             let group_start = (poly_index % k) * k; // Calculate the starting position of each group
//             let party_group = &comn_per_party[group_index][group_start..group_start + k];

//             let norms = calculate_norms_for_polynomial_vector(&vec![sampled_poly.clone()]);
//             if norms.iter().any(|&n| n > large_b) || party_group != &openck_result {
//                 return "abort".to_string();
//             }
//             poly_index += 1; // Update index after each polynomial
//         }
//     }

//     "continue".to_string()
// }

// // Function to compute the norm of each polynomial for data in Vec<Polynomial> format
// fn calculate_norms_for_polynomial_vector(polynomials: &Vec<Polynomial>) -> Vec<f64> {
//     polynomials
//         .iter()
//         .map(|poly| {
//             let mod_val_f64 = poly.mod_val.to_f64().unwrap_or(0.0); 
//             let half_mod = mod_val_f64 / 2.0;

//             poly.coeffs
//                 .iter()
//                 .fold(0.0, |acc, &coeff| {
//                     let coeff_f64 = coeff.to_f64().unwrap_or(0.0); 
//                     let adjusted_coeff = if coeff_f64 > half_mod {
//                         coeff_f64 - mod_val_f64 
//                     } else {
//                         coeff_f64
//                     };
//                     acc + adjusted_coeff.powi(2) 
//                 })
//                 .sqrt() // Calculate the square root of the sum of squares to obtain the norm
//         })
//         .collect()
// }

// Function to perform signature calculations
fn compute_signature(
    rejec_zn_result: &Vec<Vec<Polynomial>>,
    sampled_rn: &Vec<Polynomial>,
) -> (Vec<Polynomial>, Vec<Polynomial>) {
    let sign_zn = sum_polynomials_by_index(rejec_zn_result);
    let sign_rn = sum_polynomials_by_index(sampled_rn); 

    (sign_zn, sign_rn)
}

// Function to add polynomials at each index
fn sum_polynomials_by_index(sampled_vector: &Vec<Vec<Polynomial>>) -> Vec<Polynomial> {
    if sampled_vector.is_empty() {
        return Vec::new();
    }

    let num_polynomials = sampled_vector[0].len(); // Number of polynomials each party has
    let mut sum_polynomials =
        vec![Polynomial::new(vec![], sampled_vector[0][0].mod_val.clone()); num_polynomials];

    for party_polynomials in sampled_vector {
        for (index, poly) in party_polynomials.iter().enumerate() {
            sum_polynomials[index] = sum_polynomials[index].add_ref(poly);
        }
    }

    sum_polynomials
}