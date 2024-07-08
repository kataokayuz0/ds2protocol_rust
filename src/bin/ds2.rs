use num_bigint::Sign;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use num_traits::{One, Zero};
use rand::rngs::StdRng;
use rand::rngs::ThreadRng;
use rand::thread_rng;
use rand::Rng;
use rand::SeedableRng;
use rand_distr::{Distribution, Normal, Uniform};
use sha2::{Digest, Sha256};
use std::fmt::Write;
use std::ops::Sub;
use std::ops::{Add, Mul};
use std::sync::{Arc, Mutex};
use std::time::Instant;
use std::fmt;
use concrete_ntt::native128::Plan32;
use rug::{Assign, Float};
use rug::ops::{Pow};
use rand_chacha::ChaCha20Rng;

const K: usize = 2;
const L: usize = 2;
const Q: i128 = 862214684689;
// const PRIMITIVE_ROOT: i128 = 79; //原始根
const N: usize = 1024;

fn main() {
    let start = Instant::now();

    let party_number: usize = 1000;
    let a_n = generate_fromuniform_random_matrix(K, L, Q, party_number, N);
    // println!("Random matrix A_n: {:?}", a_n);

    // println!("Length of a_n: {}", a_n.len());

    let gn: Vec<String> = a_n
        .iter()
        .enumerate()
        .map(|(i, matrix)| random_oracle_commitment(matrix, i as u128))
        .collect();

    // println!("Commitment g_n: {:?}", gn);

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
    // println!("Sum of matrices A_n: {:?}", a_sum);

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

    // println!("Public random matrix A_bar: {:?}", a_bar);

    let eta: i128 = 5;
    let eta_f64: f64 = eta as f64;

    let sn: Vec<Vec<Polynomial>> = (0..party_number)
        .map(|_| sample_from_s_eta(eta, L + K, N, Q))
        .collect();

    // println!("sn: {:?}", sn);

    let tn = multiply_polynomial_matrix_vector(&a_bar, &sn, &Q);
    // println!("tn: {:?}", tn);

    let t_sum = sum_tn_matrices(&tn, &Q);
    // println!("t_sum: {:?}", t_sum);
    let size_of_t_sum = bit_size_of_polynomials_vec(&t_sum);
    println!("Size of t_sum: {}", &size_of_t_sum);

    let g_prime_n: Vec<String> = tn
        .iter()
        .enumerate()
        .map(|(i, t)| random_oracle_commitment_polynomials(t, i as u128))
        .collect();

    //println!("Sending out g'n: {:?}", g_prime_n);

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
    let pk_copy = pk.clone();
    // println!("Local output for Pn: {:?}", (sn, pk));

    let message = "example_message";

    let f64_party_number = party_number as f64;

    let alpha: f64 = 11.0 * f64_party_number * 10.0;
    let kappa_usize = 5;
    let gamma: f64 = 1.1;
    let t: f64 = 12.0;
    let n: f64 = N as f64;
    let l: f64 = L as f64;
    let k: f64 = K as f64;
    let kappa: f64 = kappa_usize as f64;

    let large_t = kappa * eta_f64 * (n * (l + k)).sqrt();
    // println!("large_t: {}", large_t);
    let sigma = &alpha * &large_t;
    // println!("sigma: {}", sigma);
    let large_b = gamma * sigma * (n * (l + k)).sqrt();

    let m_f64 = ((t / alpha) + (1.0 / (2.0 * alpha.powi(2)))).exp();
    // println!("M: {}", m_f64);
    let mn = m_f64.powf(f64_party_number);
    println!("M^n: {}", mn);
    let trapl = Q.to_f64().unwrap().log(20.0).ceil() as usize;
    let trapw = Q.to_f64().unwrap().log(20.0).ceil() as usize;
    // 標準偏差の形式をサンプラーに合わせる
    // let s = &alpha * &large_t * (2.0 * std::f64::consts::PI).sqrt();
    let s = sigma.clone();
    let sampler = GaussianSampler::new(s);

    // println!("trapl: {}, trapw: {}, s: {}", trapl, trapw, s);

    let mut last_rejec_zn_result: Option<Vec<Vec<Polynomial>>> = None;
    let mut last_derived_challenge: Option<Polynomial> = None;
    let mut sampled_rn: Vec<Vec<Polynomial>> = Vec::new();
    let mut comn_per_party: Vec<Vec<Vec<Polynomial>>> = Vec::new();
    let mut ahat: Vec<Vec<Polynomial>> = Vec::new();
    let mut wn: Vec<Vec<Polynomial>> = Vec::new();
    let mut com: Vec<Vec<Vec<Polynomial>>> = Vec::new();
    let mut computed_zn: Vec<Vec<Polynomial>> = Vec::new();
    let mut csn: Vec<Vec<Polynomial>> = Vec::new();
    let mut sample_yn: Vec<Vec<Polynomial>> = Vec::new();

    loop {
        sample_yn = sampleyn(L, K, &sampler, Q, party_number);
        // println!("sample_yn: {:?}", sample_yn);

        wn = computewn(&a_bar, &sample_yn, &Q);
        // println!("wn: {:?}", wn);
        // if !wn.is_empty() {
        //     let rows = wn.len();
        //     let cols = wn[0].len();
        //     println!("wn has {} rows and {} columns.", rows, cols);
        // } else {
        //     println!("wn is empty.");
        // }

        sampled_rn = samplern(party_number, trapl, trapw, &sampler, Q);
        // println!("sampled_rn: {:?}", sampled_rn);
        // sampled_rnの行列の大きさを確認
        let rows = sampled_rn.len();
        let cols = sampled_rn[0].len();
        println!("sampled_rn has {} rows and {} columns.", rows, cols);

        // H3関数として、cgenを使用してコミットメントキー(ck=ahat)を生成する
        ahat = c_gen(message, &pk, Q, &trapl, &trapw);
        let rows = ahat.len();
        let cols = ahat[0].len();
        println!("Commitment key ck has {} rows and {} columns.", rows, cols);

        let result = commitck(&wn, &sampled_rn, &ahat, party_number);
        // println!("result: {:?}", result);
        let (zero, comn) = result;
        comn_per_party = comn;
        let size_of_comn = bit_size_of_polynomials_vec_vec_vec(&comn_per_party);
        println!("Size of comn: {}", &size_of_comn);
        // let rows = comn_per_party.len();
        // let cols = comn_per_party[0].len();
        // println!("com_per_party: {:?}", comn_per_party);
        // println!("com_per_party has {} rows and {} columns.", rows, cols);

        com = setcom(comn_per_party.clone(), K);
        // println!("Commitment com: {:?}", com);
        let size_of_com_vec = bit_size_of_polynomials_vec_vec_vec(&com);
        println!("Size of com_vec: {}", &size_of_com_vec);

        let derived_challenge = h0(&com, message, &pk_copy, N, &kappa_usize, &Q);
        // println!("Derived challenge: {:?}", derived_challenge);

        (computed_zn, csn) = compute_zn_ntt(&derived_challenge, &sn, &sample_yn);
        // let rows = computed_zn.len();
        // let cols = computed_zn[0].len();
        // println!("rejec_zn_result has {} rows and {} columns.", rows, cols);
        // println!("computed_zn: {:?}", computed_zn);
        // println!("csn: {:?}", csn);

        match rejection_sample(&csn, &computed_zn, s, m_f64) {
            Ok(rejec_zn_result) => {
                println!("Accepted signature shares");
                let rows = rejec_zn_result.len();
                let cols = rejec_zn_result[0].len();
                // println!("rejec_zn_result has {} rows and {} columns.", rows, cols);
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
        let reconted_wj = recon_wj(&a_bar, derived_challenge, &tn, &Q, &rejec_zn_result);
        // println!("reconted_wj: {:?}", reconted_wj);
        if validate_zn(&rejec_zn_result, large_b) == "abort" {
            println!("protocol aborted by zn_value check.");
        } else if validate_openck(
            &sampled_rn,
            &reconted_wj,
            &comn_per_party.clone(),
            large_b,
            &ahat,
            K,
        ) == "abort"
        {
            println!("protocol aborted by openck check.");
        } else {
            println!("Let's go!");
            let size_of_zn = bit_size_of_polynomials_vec_vec(&rejec_zn_result);
            println!("Size of zn: {}", &size_of_zn);
            let size_of_rn = bit_size_of_polynomials_vec_vec(&sampled_rn);
            println!("Size of rn: {}", &size_of_rn);
            let (sign_zn, sign_rn) = compute_signature(&rejec_zn_result, &sampled_rn);
            let size_of_z_vec = bit_size_of_polynomials_vec(&sign_zn);
            println!("Size of z_vec: {}", &size_of_z_vec);
            let size_of_r_vec = bit_size_of_polynomials_vec(&sign_rn);
            println!("Size of r_vec: {}", &size_of_r_vec);
            // println!("sign_rn: {:?}", sign_rn);
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
            // println!("t_sum: {:?}", &pk_copy.1[0]);
            // println!("ver_w: {:?}", ver_w);
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
    } else {
        println!("No valid signature shares were generated.");
    }

    let duration = start.elapsed();
    println!("Execution time: {:?}", duration);
}

#[derive(Clone, PartialEq)]
struct Polynomial {
    coeffs: Vec<i128>, // 係数をi128型で保持
    mod_val: i128,     // 係数の剰余を取る値もi128型
}

impl Polynomial {
    // コンストラクタでmod_valが0でないことを確認
    fn new(mut coeffs: Vec<i128>, mod_val: i128) -> Self {
        if mod_val == 0 {
            panic!("mod_val cannot be zero");
        }
        // 末尾のゼロを削除
        while let Some(&last) = coeffs.last() {
            if last == 0 {
                coeffs.pop();
            } else {
                break;
            }
        }
        Polynomial { coeffs, mod_val }
    }

    // このPolynomialの情報量をビット単位で返す
    pub fn bit_size(&self) -> usize {
        let mut total_bits = 0;
        for &coeff in &self.coeffs {
            // selfを引数として渡す
            total_bits += self.bit_size_of_coeff(coeff);
        }
        total_bits
    }

    // 各係数の情報量（ビット数）を計算するヘルパーメソッド
    fn bit_size_of_coeff(&self, coeff: i128) -> usize {
        let half_mod = self.mod_val / 2;

        // 係数がmod_val / 2を超える場合、本来は負の値として扱う
        let adjusted_coeff = if coeff > half_mod {
            coeff - self.mod_val
        } else {
            coeff
        };

        if adjusted_coeff == 0 {
            1 // 0は1ビットで表現できる
        } else {
            // 係数の絶対値の対数を取り、それに基づいてビット数を計算
            let bits = (adjusted_coeff.abs() as f64).log2().ceil() as usize; // 対数を取り、切り上げる
            bits
        }
    }

    // Polynomialのデータをバイト配列に変換するメソッド
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        for &coeff in &self.coeffs {
            // 各係数をバイト配列に変換し、結果のベクターに追加する
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

    // Plan32を用いた多項式乗算を行うメソッド
    fn mul_ntt(&self, other: &Polynomial) -> Self {
        assert_eq!(self.mod_val, other.mod_val, "Modulus values must match for multiplication");
    
        let n = self.coeffs.len().max(other.coeffs.len()).next_power_of_two();
        let plan = Plan32::try_new(n).expect("Failed to create NTT plan");
    
        // 係数のパディングと型変換
        let mut lhs_padded = vec![0u128; n];
        let mut rhs_padded = vec![0u128; n];
        for (i, &coeff) in self.coeffs.iter().enumerate() {
            lhs_padded[i] = coeff as u128;
        }
        for (i, &coeff) in other.coeffs.iter().enumerate() {
            rhs_padded[i] = coeff as u128;
        }
    
        // 結果を格納するためのベクトル
        let mut prod = vec![0u128; n];
    
        // NTTによる乗算
        plan.negacyclic_polymul(&mut prod, &lhs_padded, &rhs_padded);
    
        // モジュラス Q による剰余を取り、i128へ型変換し、負の値を正の値に修正
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
            let coeff_self = *self.coeffs.get(i).unwrap_or(&0); // self.coeffs のi番目がなければ0を使用
            let coeff_other = *other.coeffs.get(i).unwrap_or(&0); // other.coeffs のi番目がなければ0を使用
            let sum = coeff_self + coeff_other;
            let modded_sum = (sum % self.mod_val + self.mod_val) % self.mod_val; // モジュロ演算後に負の値が出ないように調整
            result_coeffs[i] = modded_sum;
        }

        Polynomial::new(result_coeffs, self.mod_val)
    }

    fn sub_ref(&self, other: &Polynomial) -> Polynomial {
        let max_len = std::cmp::max(self.coeffs.len(), other.coeffs.len());
        let mut result_coeffs = vec![0i128; max_len];

        for i in 0..max_len {
            let coeff_self = *self.coeffs.get(i).unwrap_or(&0); // self.coeffs のi番目がなければ0を使用
            let coeff_other = *other.coeffs.get(i).unwrap_or(&0); // other.coeffs のi番目がなければ0を使用
            let diff = coeff_self - coeff_other;
            let modded_diff = (diff % self.mod_val + self.mod_val) % self.mod_val; // モジュロ演算後に負の値が出ないように調整
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

// 演算子オーバーロードのための参照型を使用した演算の実装
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

/// ガウスサンプリングを行うための構造体
struct GaussianSampler {
    normal: Normal<f64>,   // 標準正規分布を用いる
    rng: Mutex<ThreadRng>, // ランダム数生成器をスレッドセーフに利用
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
        let rounded_value = value.round() as i128; // f64からi128への型変換を明示
        rounded_value
    }
}

// Vec<Polynomial> の情報量を計算する関数
fn bit_size_of_polynomials_vec(polynomials: &[Polynomial]) -> usize {
    polynomials.iter().map(|p| p.bit_size()).sum()
}

// Vec<Vec<Polynomial>> の情報量を計算する関数
fn bit_size_of_polynomials_vec_vec(vec: &[Vec<Polynomial>]) -> usize {
    vec.iter().map(|inner_vec| bit_size_of_polynomials_vec(inner_vec)).sum()
}

// Vec<Vec<Vec<Polynomial>>> の情報量を計算する関数
fn bit_size_of_polynomials_vec_vec_vec(vec: &[Vec<Vec<Polynomial>>]) -> usize {
    vec.iter().map(|inner_vec_vec| bit_size_of_polynomials_vec_vec(inner_vec_vec)).sum()
}

fn uniform_sample_polynomial(q: i128, n: usize) -> Polynomial {
    let mut rng = rand::thread_rng();
    let range = Uniform::new(-(q / 2), q / 2 + 1);  // q/2 を含むために +1
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

// 一様ランダムに多項式を生成する関数(ahat行列内多項式)
fn sample_polynomial_for_ahat<R: Rng>(
    rng: &mut R,
    q: i128,
) -> Polynomial {
    let range = Uniform::new(-(q / 2), q / 2 + 1);
    let coeffs: Vec<i128> = (0..N)
        .map(|_| {
            let sample = range.sample(rng);
            (sample + q) % q // qで剰余を取る
        })
        .collect();

    Polynomial::new(coeffs, q)
}

// ガウスサンプルに基づいて多項式を生成する関数(yn、rn行列内多項式)
fn gaussian_sample_polynomial_for_yn_rn(sampler: &GaussianSampler, q: i128) -> Polynomial {
    let coeffs: Vec<i128> = (0..N)
        .map(|_| {
            let sample = sampler.sample() as i128; // サンプリングされた整数をf64にキャスト
            let signed_sample = if thread_rng().gen::<bool>() {
                q + sample
            } else {
                q - sample
            };
            signed_sample % q // qで剰余を取る
        })
        .collect();

    Polynomial::new(coeffs, q)
}

// kxlのランダム多項式行列を生成し、それらをparty_numberの数だけリストに格納する関数
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
            .map(|_| sample_polynomial_for_ahat(rng, q))
            .collect();
        matrices.push(matrix);
    }
    matrices
}

// 可逆な1*1行列を返す関数
fn generate_invertible_matrix<R: Rng>(
    rng: &mut R,
    q: i128,
) -> Vec<Vec<Polynomial>> {
    loop {
        let ahat1_1: Vec<Vec<Polynomial>> = vec![vec![sample_polynomial_for_ahat(rng, q)]];
        // For 1*1 matrices, we assume here that the polynomial is "invertible" by checking that it is non-zero
        if !ahat1_1[0][0].coeffs[0].is_zero() {
            return ahat1_1;
        }
    }
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

// etaの範囲でランダムな係数を持つ多項式を生成する関数
fn sample_from_s_eta(eta: i128, size: usize, n: usize, mod_val: i128) -> Vec<Polynomial> {
    let mut rng = thread_rng();
    let range = Uniform::new_inclusive(-eta, eta);
    (0..size)
        .map(|_| {
            let coeffs = (0..n).map(|_| {
                let coeff = range.sample(&mut rng); // 四捨五入を追加
                let modded_coeff = ((coeff % mod_val) + mod_val) % mod_val;
                modded_coeff
            }).collect();
            Polynomial::new(coeffs, mod_val)
        })
        .collect()
}

// ランダムオラクルコミットメントを生成する関数
fn random_oracle_commitment(matrix: &Vec<Polynomial>, party_number: u128) -> String {
    // 行列の各要素（多項式の文字列表現）を文字列に変換して結合
    let mut combined = String::new();
    for poly in matrix {
        write!(&mut combined, "{}", poly.to_string()).expect("Failed to write to string");
    }
    // パーティ番号を文字列に変換して結合
    write!(&mut combined, "{}", party_number).expect("Failed to write to string");
    // SHA256ハッシュを計算
    let mut hasher = Sha256::new();
    hasher.update(combined.as_bytes());
    let hash_result = hasher.finalize();
    // ハッシュ値を16進数の文字列に変換
    format!("{:x}", hash_result)
}

// KxLのランダム多項式行列の合計を計算し、新しい行列を返す関数
fn sum_matrices(matrices: &Vec<Vec<Polynomial>>) -> Vec<Polynomial> {
    // 入力が空の場合は空のベクトルを返す
    if matrices.is_empty() || matrices[0].is_empty() {
        return Vec::new();
    }

    let k = matrices[0].len(); // 最初の行列の行数でKを設定
    let mod_val = matrices[0][0].mod_val; // 最初の多項式のmod_valを使用
    let n = matrices[0][0].coeffs.len(); // 最初の多項式の係数の数でNを設定

    // mod_valとNを使用してsum_matrixを初期化
    let mut sum_matrix = vec![Polynomial::new(vec![0; n], mod_val); k];

    // 各行列について同じ位置の多項式を合計する
    for matrix in matrices {
        for (i, poly) in matrix.iter().enumerate() {
            sum_matrix[i] = sum_matrix[i].clone() + poly.clone();
        }
    }

    sum_matrix
}

fn sum_tn_matrices(tn: &Vec<Vec<Polynomial>>, q: &i128) -> Vec<Polynomial> {
    if tn.is_empty() {
        return Vec::new();
    }

    // 列の数を決定
    let num_cols = tn[0].len();
    let mut result = vec![Polynomial::new(vec![0], q.clone()); num_cols];

    // 各ベクトルの同じ位置の多項式を加算
    for vec in tn {
        for (i, poly) in vec.iter().enumerate() {
            result[i] = result[i].clone().add(poly.clone());
        }
    }

    result
}

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

//a. sample yn and compute wn
// `sampleyn` 関数: 各パーティごとに (l+k) * 1 の多項式ベクトルを生成
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

// `computewn` 関数: a_bar と sample_yn の乗算を行い、結果を k * 1 のベクトルで返す
fn computewn(
    a_bar: &Vec<Vec<Polynomial>>,
    sample_yn: &Vec<Vec<Polynomial>>,
    q: &i128,
) -> Vec<Vec<Polynomial>> {
    multiply_polynomial_matrix_vector(a_bar, sample_yn, q)
}

//b. compute comn with rn

// `samplern` 関数: 各パーティごとに (trapl+2trapw) の長さを持つ多項式ベクトルを生成
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

// CGen関数の改修版
fn c_gen(message: &str, pk: &(Vec<Polynomial>, Vec<Polynomial>), q: i128, trapl: &usize, trapw: &usize) -> Vec<Vec<Polynomial>> {
    // メッセージと公開鍵からハッシュ値を計算して乱数生成器を初期化
    let mut hasher = Sha256::new();
    hasher.update(message.as_bytes());
    for poly in &pk.0 {
        hasher.update(poly.to_bytes()); // Polynomialのバイト表現
    }
    for poly in &pk.1 {
        hasher.update(poly.to_bytes()); // Polynomialのバイト表現
    }
    let result = hasher.finalize();
    let seed = u64::from_ne_bytes(result[0..8].try_into().unwrap());
    let mut rng = ChaCha20Rng::seed_from_u64(seed);

    // 可逆な1*1行列を生成
    let ahat1_1 = generate_invertible_matrix(&mut rng, q);
    let mut ahat1_j = generate_random_matrix(&mut rng,1, trapl + 2 * trapw - 1, q, 1)[0].clone();

    let mut first_row = vec![ahat1_1[0][0].clone()];
    first_row.append(&mut ahat1_j);

    let list1 = vec![
        Polynomial::new(vec![0], q),
        Polynomial::new(vec![1], q),
    ];
    let mut ahat2_j = generate_random_matrix(&mut rng,1, trapl + 2 * trapw - 2, q, 1)[0].clone();

    let mut second_row = list1;
    second_row.append(&mut ahat2_j);

    vec![first_row, second_row]
}

// Function to calculate commitment
fn commitck(
    flat_wn: &Vec<Vec<Polynomial>>,
    sampled_rn: &Vec<Vec<Polynomial>>,
    ahat: &Vec<Vec<Polynomial>>,
    party_number: usize,
) -> (Vec<Vec<Polynomial>>, Vec<Vec<Vec<Polynomial>>>) {
    let mut comn_per_party = vec![Vec::new(); party_number]; 

    for (p, (temp_wn, sampled_rn_poly)) in flat_wn.iter().zip(sampled_rn.iter()).enumerate() {

        for (poly, sampled_poly) in temp_wn.iter().zip(sampled_rn_poly.iter()) {
            let fleft = multiply_ahat_with_sampled_matrix(ahat, &sampled_poly.clone());
            // println!("fleft: {:?}", fleft);
            let fright_poly_matrix = combine_matrices_vertically(
                &vec![Polynomial::new(vec![0], ahat[0][0].mod_val.clone())],
                &vec![poly.clone()],
            );
            // println!("fright_poly_matrix: {:?}", fright_poly_matrix);

            let formatted_fleft = format_openck_fleft(fleft);
            // println!("formatted_fleft: {:?}", formatted_fleft);
            let f = add_formatted_matrices(&formatted_fleft, &fright_poly_matrix);

            let party_index = p % party_number;
            comn_per_party[party_index].extend(f);
        }
    }

    let matrix_zero = vec![vec![Polynomial::new(vec![0], ahat[0][0].mod_val.clone())]];
    return (matrix_zero, comn_per_party);
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

fn combine_matrices_vertically(
    matrix_zero: &Vec<Polynomial>,
    reconted_wj: &Vec<Polynomial>,
) -> Vec<Vec<Vec<Polynomial>>> {
    let mut combined_matrix = Vec::new();

    for index in 0..matrix_zero.len() {
        let mut combined_row = Vec::new();
        combined_row.push(vec![matrix_zero[index].clone()]);
        combined_row.push(vec![reconted_wj[index].clone()]);
        combined_matrix.push(combined_row);
    }

    combined_matrix
}

// Change fleft format to avoid extra nesting
fn format_openck_fleft(openck_fleft: Vec<Vec<Polynomial>>) -> Vec<Vec<Vec<Polynomial>>> {
    vec![openck_fleft]
}

// Fix function that adds two multilayer matrices and returns a flat matrix 
fn add_formatted_matrices(
    matrix1: &Vec<Vec<Vec<Polynomial>>>,
    matrix2: &Vec<Vec<Vec<Polynomial>>>,
) -> Vec<Vec<Polynomial>> {
    let mut combined_matrix = Vec::new();

    for (rows1, rows2) in matrix1.iter().zip(matrix2.iter()) {
        for (row1, row2) in rows1.iter().zip(rows2.iter()) {
            let mut combined_row = Vec::new();
            for (poly1, poly2) in row1.iter().zip(row2.iter()) {
                combined_row.push(poly1.add_ref(poly2));
            }
            combined_matrix.push(combined_row);
        }
    }

    combined_matrix
}


//a. set com
// Function to calculate total commitment from comn_per_party
fn setcom(comn_per_party: Vec<Vec<Vec<Polynomial>>>, k: usize) -> Vec<Vec<Vec<Polynomial>>> {
    if comn_per_party.is_empty() {
        return Vec::new();
    }

    let num_rows = comn_per_party[0].len();
    let num_cols = if num_rows > 0 {
        comn_per_party[0][0].len()
    } else {
        0
    };

    // Changed initialization method to store results in a two-dimensional list instead of a one-dimensional list
    let mut grouped_results = vec![Vec::new(); num_rows / k]; // k個ずつグループ化するための二次元ベクター

    // Create a flat list to store temporary results
    let mut temp_results = vec![vec![Polynomial::new(vec![0], Q); num_cols]; num_rows];

    // Adds up all the elements of the input data
    for party_coms in comn_per_party {
        for (i, row_coms) in party_coms.iter().enumerate() {
            for (j, com) in row_coms.iter().enumerate() {
                temp_results[i][j] = temp_results[i][j].add_ref(com);
            }
        }
    }

    // Divide one-dimensional results into two-dimensional groups
    for (i, result) in temp_results.iter().enumerate() {
        let group_index = i / k; 
        grouped_results[group_index].push(result.clone()); 
    }

    grouped_results
}

//b. derive challenge
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

    positions.sort(); // 位置をソートして一貫性を保つ

    let mut coeffs = vec![0; n];
    for &pos in &positions {
        coeffs[pos] = if rng.gen() { 1 } else { q - 1 };
    }

    Polynomial::new(coeffs, q.clone())
}

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
                    let mut product = derived_challenge.clone().mul_ntt(&poly.clone()); // derived_challengeをcloneして乗算
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

    // 値が非常に小さくなってしまうため、先にexp内部の計算を行う
    // 外側のベクトル（パーティごとのリスト）に対してループ
    for (csn_party, zn_party) in csn_list.iter().zip(zn_list.iter()) {

        // 各パーティの全体ベクトルを作成
        let csn_combined: Vec<f64> = csn_party.iter().flat_map(|poly| polynomial_to_f64_vec(poly)).collect();
        let zn_combined: Vec<f64> = zn_party.iter().flat_map(|poly| polynomial_to_f64_vec(poly)).collect();

        // 各パーティに対してノルムを計算
        let (rohs_zn, rohcsn_s_zn) = calculate_sums_for_poly(&csn_combined, &zn_combined, s);
        // println!("rohs_rm: {}", rohs_rm);
        // println!("rohcsn_s_rm: {}", rohcsn_s_rm);
        rohs_zns.push(rohs_zn);
        rohcsn_s_zns.push(rohcsn_s_zn);
        sum_rohs_zn += rohs_zn;
        sum_rohcsn_s_zn += rohcsn_s_zn;

    }

    for ((rohs_zn, rohcsn_s_zn), zn_list) in rohs_zns.iter().zip(rohcsn_s_zns.iter()).zip(zn_list.iter()) {
        // 各パーティに対して拒否サンプリングを実行
        let ratio = ((rohs_zn / sum_rohs_zn).exp()) / (m * ((rohcsn_s_zn / sum_rohcsn_s_zn).exp()));
        // println!("Ratio: {}", ratio);

        // 比率と1の小さい方を選ぶ
        let acceptance_probability = ratio.min(1.0);
        let random_probability: f64 = rand::random();

        // ランダムな確率を使用してサンプルを受け入れるか拒否するかを決定
        if random_probability <= acceptance_probability {
            rejec_zn_party_result.push(zn_list.clone());
        } else {
            // 拒否された場合は再サンプリングが必要
            return Err("restart");
        }
    }
    Ok(rejec_zn_party_result)
}

// 単一の多項式のための比率計算関数を任意精度で計算
fn calculate_sums_for_poly(csn: &Vec<f64>, zn: &Vec<f64>, s: f64) -> (f64, f64) {
    let precision = 50; // 50ビットの精度
    let pi = Float::with_val(precision, std::f64::consts::PI);
    let s = Float::with_val(precision, s);

    let zn_norm = Float::with_val(precision, calculate_norm(zn));
    let csn_minus_zn = sub_ref_f64(zn, csn);
    let csn_norm = Float::with_val(precision, calculate_norm(&csn_minus_zn));

    let zn_norm_squared: Float = zn_norm.clone().pow(2); // 明示的な型注釈
    let s_squared: Float = s.clone().pow(2); // 明示的な型注釈
    let csn_norm_squared: Float = csn_norm.pow(2); // 明示的な型注釈

    let rohs_zn = -(zn_norm_squared / (Float::with_val(precision, 2.0) * s_squared.clone()));
    let rohcsn_s_zn = -(csn_norm_squared / (Float::with_val(precision, 2.0)* s_squared.clone()));

    // Floatからf64への変換
    (rohs_zn.to_f64(), rohcsn_s_zn.to_f64())
}

// 多項式をf64のベクトルに変換する関数
fn polynomial_to_f64_vec(poly: &Polynomial) -> Vec<f64> {
    let half_mod_val = poly.mod_val / 2; // モジュラスの半分

    poly.coeffs
        .iter()
        .map(|&coeff| {
            let adjusted_coeff = if coeff > half_mod_val {
                // 係数がモジュラスの半分を超えている場合、マイナスの値として解釈
                (coeff as i128 - poly.mod_val) as f64
            } else {
                // それ以外の場合、そのまま正の値として解釈
                coeff as f64
            };
            adjusted_coeff // i128からf64へキャスト
        })
        .collect()
}

// ベクトルのノルムを計算する関数
fn calculate_norm(vec: &Vec<f64>) -> f64 {
    vec.iter().map(|&x| x * x).sum::<f64>().sqrt()
}

// Vec<f64> の要素間で減算を行い，結果のVec<f64> を返す
fn sub_ref_f64(a: &Vec<f64>, b: &Vec<f64>) -> Vec<f64> {
    let max_len = std::cmp::max(a.len(), b.len());
    let mut result = vec![0.0; max_len];

    for i in 0..max_len {
        let a_val = *a.get(i).unwrap_or(&0.0); // a の i 番目がなければ 0.0 を使用
        let b_val = *b.get(i).unwrap_or(&0.0); // b の i 番目がなければ 0.0 を使用
        result[i] = a_val - b_val;
    }

    result
}

fn validate_zn(zn_result: &Vec<Vec<Polynomial>>, large_b: f64) -> String {
    for zn_party in zn_result {
        // 各パーティの多項式ベクトルを一つの大きなベクトルに結合
        let combined_coeffs: Vec<f64> = zn_party
            .iter()
            .flat_map(|poly| polynomial_to_f64_vec(poly))
            .collect();

        // 結合されたベクトルのノルムを計算
        let zn_norm = calculate_norm(&combined_coeffs);
        // println!("Combined zn_norm: {}", zn_norm);
        // println!("large_b: {}", large_b);

        // ノルムがlarge_bより大きい場合は処理を中断
        if zn_norm > large_b {
            return "abort".to_string();
        }
    }
    "continue".to_string()
}

// `recon_wj` 関数内の該当部分を修正
fn recon_wj(
    a_bar: &Vec<Vec<Polynomial>>,
    challenge: &Polynomial,
    tn: &Vec<Vec<Polynomial>>,
    q: &i128,
    zn: &Vec<Vec<Polynomial>>,
) -> Vec<Vec<Polynomial>> {
    let mut reconted_wj = Vec::new();

    // challenge * tn を計算し、正しい形式で保存する
    let recon_wn_rights: Vec<Vec<Polynomial>> = tn
        .iter()
        .map(|tn_row| {
            tn_row
                .iter()
                .map(|tn_poly| {
                    let mut product = challenge.clone().mul_ntt(&tn_poly.clone());
                    product
                })
                .collect()
        })
        .collect();

    //a_barとznの乗算を行い，その結果を保存
    let addition_result = multiply_polynomial_matrix_vector(a_bar, zn, q);

    // 最終的な結果として addition_result から recon_wn_rights を減算
    for (addition_row, recon_wn_right_row) in addition_result.iter().zip(recon_wn_rights.iter()) {
        let reconted_row: Vec<Polynomial> = addition_row
            .iter()
            .zip(recon_wn_right_row)
            .map(|(addition_poly, recon_wn_right_poly)| {
                let mut result = addition_poly.clone().sub(recon_wn_right_poly.clone());
                result
            })
            .collect();
        reconted_wj.push(reconted_row);
    }

    reconted_wj
}

fn validate_openck(
    sampled_rn: &Vec<Vec<Polynomial>>,
    reconted_wj: &Vec<Vec<Polynomial>>,
    comn_per_party: &Vec<Vec<Vec<Polynomial>>>,
    large_b: f64,
    ahat: &Vec<Vec<Polynomial>>,
    k: usize, // グループサイズ k をパラメータとして追加
) -> String {
    let mut poly_index = 0; // 全体のポリノミアルインデックスを追跡する変数

    for (j, (temp_reconted_wj, temp_sampled_rn)) in reconted_wj.iter().zip(sampled_rn.iter()).enumerate() {

        for (_poly, sampled_poly) in temp_reconted_wj.iter().zip(temp_sampled_rn.iter()) {
            let openck_fleft = multiply_ahat_with_sampled_matrix(ahat, &sampled_poly.clone());
            // println!("openck_fleft: {:?}", openck_fleft);
            let openck_zero_x = combine_matrices_vertically(
                &vec![Polynomial::new(vec![0], ahat[0][0].mod_val.clone())],
                &vec![_poly.clone()],
            );
            // println!("openck_zero_x: {:?}", openck_zero_x);
            let formatted_openck_fleft = format_openck_fleft(openck_fleft);
            let openck_result = add_formatted_matrices(&formatted_openck_fleft, &openck_zero_x);

            // 正しい comn_per_party のセグメントを計算するために poly_index を使用
            let group_index = poly_index / k; // 各サブリストにおけるポリノミアルグループのインデックスを計算
            let group_start = (poly_index % k) * k; // 各グループの開始位置を計算
            let party_group = &comn_per_party[group_index][group_start..group_start + k];
            // println!("openck_result: {:?}", openck_result);
            // println!("party_group: {:?}", party_group);

            let norms = calculate_norms_for_polynomial_vector(&vec![sampled_poly.clone()]);
            if norms.iter().any(|&n| n > large_b) || party_group != &openck_result {
                return "abort".to_string();
            }
            poly_index += 1; // 各多項式の後にインデックスを更新
        }
    }

    "continue".to_string()
}

// Vec<Polynomial>形式のデータに対して各多項式のノルムを計算する関数
fn calculate_norms_for_polynomial_vector(polynomials: &Vec<Polynomial>) -> Vec<f64> {
    polynomials
        .iter()
        .map(|poly| {
            let mod_val_f64 = poly.mod_val.to_f64().unwrap_or(0.0); // mod_valをf64に変換
            let half_mod = mod_val_f64 / 2.0;

            poly.coeffs
                .iter()
                .fold(0.0, |acc, &coeff| {
                    let coeff_f64 = coeff.to_f64().unwrap_or(0.0); // BigUintからf64への変換
                    let adjusted_coeff = if coeff_f64 > half_mod {
                        coeff_f64 - mod_val_f64 // mod_valの半分を超える場合、負の値として処理
                    } else {
                        coeff_f64
                    };
                    acc + adjusted_coeff.powi(2) // 二乗和を累積
                })
                .sqrt() // 二乗和の平方根を計算してノルムを得る
        })
        .collect()
}

fn compute_signature(
    rejec_zn_result: &Vec<Vec<Polynomial>>,
    sampled_rn: &Vec<Vec<Polynomial>>,
) -> (Vec<Polynomial>, Vec<Polynomial>) {
    let sign_zn = sum_polynomials_by_index(rejec_zn_result);
    let sign_rn = sum_polynomials_by_index(sampled_rn); 

    (sign_zn, sign_rn) // 修正: 結果をベクトル形式で返す
}

// 各インデックスの多項式を加算する関数
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


    // H3関数として、cgenを使用してcommitment_keyの計算
    let ready_ck = c_gen(message, &pk, Q, trapl, trapw);
    // println!("ready_ck: {:?}", ready_ck);


    // challengeの計算
    let ready_derived_challenge = h0(&com, message, &pk, N, kappa, &Q);
    // println!("ready_derived_challenge: {:?}", ready_derived_challenge);

    // a_bar とsign_znの乗算
    let ready_w_left: Vec<Polynomial> = multiply_polynomial_matrix_with_vector(a_bar, sign_zn, q);

    // challengeとt_sumの乗算
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

// 多項式行列とベクトルの乗算関数
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

fn eachparty_openck(
    sign_rn: &Vec<Polynomial>,
    ver_w: &Vec<Polynomial>,
    com: &Vec<Vec<Vec<Polynomial>>>,
    ahat: &Vec<Vec<Polynomial>>, // Ahatを加える
    bn: f64,
    k: usize,
) -> Result<(), String> {
    let sign_rn_norms = calculate_norms_for_polynomial_vector(sign_rn);
    // println!("sign_rn_norms: {:?}", sign_rn_norms);

    for j in 0..(k - 1) {
        let each_openck_fleft = multiply_ahat_with_sampled_matrix(ahat, &sign_rn[0]);
        // println!("each_openck_fleft: {:?}", each_openck_fleft);

        let temp_ver_w = &ver_w[j]; // 直接参照を使用
                                    // println!("temp_ver_w: {:?}", temp_ver_w);

        let cols = 1;
        let temp_matrix_zero = vec![Polynomial::new(vec![0], ahat[0][0].mod_val.clone()); cols]; // 0多項式のベクトルを作成

        // 各要素を正しく組み合わせる
        let each_openck_zero_x = ver_combine_matrices_vertically(&temp_matrix_zero, temp_ver_w);
        // println!("each_openck_zero_x: {:?}", each_openck_zero_x);

        let each_openck_result = add_polynomial_matrices(&each_openck_fleft, &each_openck_zero_x);
        //println!("each_openck_result[j]: {:?}", each_openck_result[j]);
        // println!("each_openck_result: {:?}", each_openck_result);

        // println!("com[j]: {:?}", com[j]);
        // println!("com: {:?}", com);
        // println!("each_openck_result_flat: {:?}", each_openck_result_flat);

        // println!("bn: {}", bn);
        // println!("sign_rn_norms: {:?}", sign_rn_norms[0]);

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

// Vec<Vec<Polynomial>>型の二つの行列を加算する関数
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
                    poly1.add_ref(&poly2) // 既存のadd_ref関数を使用して多項式を加算
                })
                .collect()
        })
        .collect()
}

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

fn eachparty_verification(
    sign_zn: &Vec<Polynomial>,
    com: &Vec<Vec<Vec<Polynomial>>>,
    sign_rn: &Vec<Polynomial>,
    ver_w: &Vec<Polynomial>,
    ahat: &Vec<Vec<Polynomial>>,
    b: f64,
    party_number: usize,
) {
    // sign_znの全要素で最大のノルムを計算
    let zn_norm = calculate_norms_for_polynomial_vector(sign_zn);
    // println!("Norm of sign_zn: {}", zn_norm[0]);
    let bn = (party_number as f64).sqrt() * b;
    // println!("Threshold bn for party {}", bn);

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
