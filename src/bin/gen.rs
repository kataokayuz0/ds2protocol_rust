use rand::thread_rng;
use rand_distr::{Distribution, Uniform};
use sha2::{Digest, Sha256};
use std::fmt::Write;
use std::ops::Sub;
use std::ops::{Add, Mul};
use std::fmt;
use concrete_ntt::native128::Plan32;

const K: usize = 2;
const L: usize = 2;
const Q: i128 = 862214684689;
// const PRIMITIVE_ROOT: i128 = 79; // primitive root of Q
const N: usize = 1024;

fn main() {

    let party_number: usize = 1000;
    let a_n = generate_fromuniform_random_matrix(K, L, Q, party_number, N);

    let gn: Vec<String> = a_n
        .iter()
        .enumerate()
        .map(|(i, matrix)| random_oracle_commitment(matrix, i as u128))
        .collect();

    let mut abort_flag = false;
    for j in 0..(party_number - 1) {
        if random_oracle_commitment(&a_n[j], j as u128) != gn[j] {
            abort_flag = true;
            break;
        }
    }

    if abort_flag {
        println!("Sending out: abort");
    } else {
        println!("Sending out: continue");
    }

    let a_sum = sum_matrices(&a_n);

    let i_matrix: Vec<Vec<i128>> = (0..K)
        .map(|i| (0..K).map(|j| if i == j { 1 } else { 0 }).collect())
        .collect();

    let a_bar: Vec<Vec<Polynomial>> = a_sum
        .iter()
        .zip(i_matrix.iter())
        .map(|(a_elem, i_row)| {
            let mut row = vec![a_elem.clone()];
            let i_row_poly: Vec<Polynomial> = i_row
                .iter()
                .map(|x| Polynomial::new(vec![x.clone()], Q.clone()))
                .collect();
            row.extend(i_row_poly);
            row
        })
        .collect();

    let eta: i128 = 5;

    let sn: Vec<Vec<Polynomial>> = (0..party_number)
        .map(|_| sample_from_s_eta(eta, L + K, N, Q))
        .collect();

    let tn = multiply_polynomial_matrix_vector(&a_bar, &sn, &Q);

    let t_sum = sum_tn_matrices(&tn, &Q);

    let g_prime_n: Vec<String> = tn
        .iter()
        .enumerate()
        .map(|(i, t)| random_oracle_commitment_polynomials(t, i as u128))
        .collect();

    let mut abort_flag = false;
    for (j, t) in tn.iter().enumerate() {
        let commitment = random_oracle_commitment_polynomials(t, j as u128);
        if commitment != g_prime_n[j] {
            abort_flag = true;
            break;
        }
    }

    if abort_flag {
        println!("Sending out: abort");
    } else {
        println!("commitment is verified.")
    }

    let pk:(Vec<Polynomial>, Vec<Polynomial>) = (a_sum.clone(), t_sum.clone());
    println!("Local output for Pn: {:?}", (sn, pk));
}

#[derive(Clone, PartialEq)]
struct Polynomial {
    coeffs: Vec<i128>, 
    mod_val: i128,    
}

impl Polynomial {
    fn new(mut coeffs: Vec<i128>, mod_val: i128) -> Self {
        if mod_val == 0 {
            panic!("mod_val cannot be zero");
        }
        // Delete trailing zeros
        while let Some(&last) = coeffs.last() {
            if last == 0 {
                coeffs.pop();
            } else {
                break;
            }
        }
        Polynomial { coeffs, mod_val }
    }

    // Method to convert Polynomial data into a byte array
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        for &coeff in &self.coeffs {
            // Convert each coefficient to a byte array and add to the resulting vector
            bytes.extend_from_slice(&coeff.to_le_bytes());
        }
        bytes
    }

    fn to_string(&self) -> String {
        self.coeffs
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<String>>()
            .join(" ")
    }

    // The method to perform polynomial multiplication using Plan32
    fn mul_ntt(&self, other: &Polynomial) -> Self {
        assert_eq!(self.mod_val, other.mod_val, "Modulus values must match for multiplication");
    
        let n = self.coeffs.len().max(other.coeffs.len()).next_power_of_two();
        let plan = Plan32::try_new(n).expect("Failed to create NTT plan");
    
        // The padding of coefficients and type conversion
        let mut lhs_padded = vec![0u128; n];
        let mut rhs_padded = vec![0u128; n];
        for (i, &coeff) in self.coeffs.iter().enumerate() {
            lhs_padded[i] = coeff as u128;
        }
        for (i, &coeff) in other.coeffs.iter().enumerate() {
            rhs_padded[i] = coeff as u128;
        }
    
        // The vector to store the result
        let mut prod = vec![0u128; n];
    
        // Multiplies using NTT
        plan.negacyclic_polymul(&mut prod, &lhs_padded, &rhs_padded);
    
        // Take modulus Q modulus, type convert to i128, and correct negative values to positive values
        let mod_prod = prod.iter().map(|&x| {
            let res = (x as i128 % self.mod_val + self.mod_val) % self.mod_val;
            if res < 0 { res + self.mod_val } else { res }
        }).collect();
    
        Polynomial::new(mod_prod, self.mod_val)
    }
    

    fn add_ref(&self, other: &Polynomial) -> Polynomial {
        let max_len = std::cmp::max(self.coeffs.len(), other.coeffs.len());
        let mut result_coeffs = vec![0i128; max_len];

        for i in 0..max_len {
            let coeff_self = *self.coeffs.get(i).unwrap_or(&0); // Use 0 if there is no i-th self.coeffs
            let coeff_other = *other.coeffs.get(i).unwrap_or(&0); // Use 0 if there is no i-th other.coeffs
            let sum = coeff_self + coeff_other;
            let modded_sum = (sum % self.mod_val + self.mod_val) % self.mod_val; // Adjustment to avoid negative values after modulo operation
            result_coeffs[i] = modded_sum;
        }

        Polynomial::new(result_coeffs, self.mod_val)
    }

    fn sub_ref(&self, other: &Polynomial) -> Polynomial {
        let max_len = std::cmp::max(self.coeffs.len(), other.coeffs.len());
        let mut result_coeffs = vec![0i128; max_len];

        for i in 0..max_len {
            let coeff_self = *self.coeffs.get(i).unwrap_or(&0);
            let coeff_other = *other.coeffs.get(i).unwrap_or(&0); 
            let diff = coeff_self - coeff_other;
            let modded_diff = (diff % self.mod_val + self.mod_val) % self.mod_val;
            result_coeffs[i] = modded_diff;
        }

        Polynomial::new(result_coeffs, self.mod_val)
    }
}

impl fmt::Debug for Polynomial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Polynomial")
         .field("coeffs", &self.coeffs)
         .field("coeffs_len", &self.coeffs.len())
         .field("mod_val", &self.mod_val)
         .finish()
    }
}

impl Add for Polynomial {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        self.add_ref(&other)
    }
}

impl Sub for Polynomial {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        &self - &other
    }
}

// Implementation of operations using reference types for operator overloading
impl<'a, 'b> Sub<&'b Polynomial> for &'a Polynomial {
    type Output = Polynomial;

    fn sub(self, other: &'b Polynomial) -> Self::Output {
        self.sub_ref(other)
    }
}

impl<'a, 'b> Mul<&'b Polynomial> for &'a Polynomial {
    type Output = Polynomial;

    fn mul(self, other: &'b Polynomial) -> Self::Output {
        self.mul_ntt(other)
    }
}

impl Mul for Polynomial {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        self.mul_ntt(&other)
    }
}

impl Mul<Polynomial> for &Polynomial {
    type Output = Polynomial;

    fn mul(self, other: Polynomial) -> Self::Output {
        self.mul_ntt(&other)
    }
}

impl Mul<&Polynomial> for Polynomial {
    type Output = Self;

    fn mul(self, other: &Polynomial) -> Self::Output {
        self.mul_ntt(other)
    }
}

// Sample a polynomial uniformly at random 
fn uniform_sample_polynomial(q: i128, n: usize) -> Polynomial {
    let mut rng = rand::thread_rng();
    let range = Uniform::new(-(q / 2), q / 2 + 1); // Uniform distribution from -(q/2) to q/2
    let coeffs: Vec<i128> = (0..n)
        .map(|_| {
            let sample = range.sample(&mut rng);
            (sample + q) % q 
        })
        .collect();

    Polynomial::new(coeffs, q)
}

fn generate_fromuniform_random_matrix(k: usize, l: usize, q: i128, party_number: usize, n: usize) -> Vec<Vec<Polynomial>> {
    let mut matrices: Vec<Vec<Polynomial>> = Vec::with_capacity(party_number);
    for _ in 0..party_number {
        let matrix: Vec<Polynomial> = (0..k * l)
            .map(|_| uniform_sample_polynomial(q, n))
            .collect();
        matrices.push(matrix);
    }
    matrices
}
// Multiply a polynomial matrix by a vector of polynomials
fn multiply_polynomial_matrix_vector(
    matrix: &[Vec<Polynomial>],
    vector: &[Vec<Polynomial>],
    mod_value: &i128,
) -> Vec<Vec<Polynomial>> {
    let num_columns = vector.len(); // vectorの行数
    let mut result = Vec::with_capacity(num_columns);

    for column in 0..num_columns {
        let mut column_result = Vec::new();

        for matrix_row in matrix.iter() {
            let mut result_poly = Polynomial::new(vec![0; matrix_row[0].coeffs.len()], *mod_value);

            // matrixの行とvectorの特定の列の要素ごとの乗算と加算
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

// Generate a polynomial with random coefficients in the range of eta
fn sample_from_s_eta(eta: i128, size: usize, n: usize, mod_val: i128) -> Vec<Polynomial> {
    let mut rng = thread_rng();
    let range = Uniform::new_inclusive(-eta, eta);
    (0..size)
        .map(|_| {
            let coeffs = (0..n).map(|_| {
                let coeff = range.sample(&mut rng); 
                let modded_coeff = ((coeff % mod_val) + mod_val) % mod_val;
                modded_coeff
            }).collect();
            Polynomial::new(coeffs, mod_val)
        })
        .collect()
}

// Generate a random oracle commitment
fn random_oracle_commitment(matrix: &Vec<Polynomial>, party_number: u128) -> String {
    // Converts each element of a matrix to a string and joins them
    let mut combined = String::new();
    for poly in matrix {
        write!(&mut combined, "{}", poly.to_string()).expect("Failed to write to string");
    }
    // Convert party number to string and merge
    write!(&mut combined, "{}", party_number).expect("Failed to write to string");
    // Calculate SHA256 hash
    let mut hasher = Sha256::new();
    hasher.update(combined.as_bytes());
    let hash_result = hasher.finalize();
    // Convert hash value to hexadecimal string
    format!("{:x}", hash_result)
}

// Calculate the sum of KxL random polynomial matrices and return a new matrix
fn sum_matrices(matrices: &Vec<Vec<Polynomial>>) -> Vec<Polynomial> {
    // Returns an empty vector if input is empty
    if matrices.is_empty() || matrices[0].is_empty() {
        return Vec::new();
    }

    let k = matrices[0].len(); 
    let mod_val = matrices[0][0].mod_val; 
    let n = matrices[0][0].coeffs.len(); 

    // Initialize sum_matrix using mod_val and N
    let mut sum_matrix = vec![Polynomial::new(vec![0; n], mod_val); k];

    // Sum the polynomials in the same position for each matrix
    for matrix in matrices {
        for (i, poly) in matrix.iter().enumerate() {
            sum_matrix[i] = sum_matrix[i].clone() + poly.clone();
        }
    }

    sum_matrix
}

// Calculate the sum of tn matrices and return a new matrix
fn sum_tn_matrices(tn: &Vec<Vec<Polynomial>>, q: &i128) -> Vec<Polynomial> {
    if tn.is_empty() {
        return Vec::new();
    }

    let num_cols = tn[0].len();
    let mut result = vec![Polynomial::new(vec![0], q.clone()); num_cols];

    for vec in tn {
        for (i, poly) in vec.iter().enumerate() {
            result[i] = result[i].clone().add(poly.clone());
        }
    }

    result
}

// Generate a random oracle commitment for a vector of polynomials
fn random_oracle_commitment_polynomials(
    polynomials: &Vec<Polynomial>,
    party_number: u128,
) -> String {
    let mut combined = String::new();
    for poly in polynomials {
        write!(&mut combined, "{}", poly.to_string()).expect("Failed to write to string");
    }
    write!(&mut combined, "{}", party_number).expect("Failed to write to string");
    let mut hasher = Sha256::new();
    hasher.update(combined.as_bytes());
    let hash_result = hasher.finalize();
    format!("{:x}", hash_result)
}