use nalgebra::DMatrix;
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
use std::f64::consts::PI;
use std::fmt::Write;
use std::ops::Sub;
use std::ops::{Add, Mul};
use std::sync::{Arc, Mutex};
use std::time::Instant;
use std::fmt;
use concrete_ntt::native128::Plan32;

const K: usize = 2;
const L: usize = 1;
const Q: i128 = 79164837199873;
// const PRIMITIVE_ROOT: i128 = 79; //原始根
const N: usize = 256;

fn main() {
    let start = Instant::now();

    let sigma_gen: i128 = 3;
    let sampler = TableSampler::new(sigma_gen);
    let party_number: usize = 2;

    let a_n = generate_random_matrix_fromtable(K, L, &sampler, Q, party_number);
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
    let eta_clone: f64 = eta as f64;

    let sn: Vec<Vec<Polynomial>> = (0..party_number)
        .map(|_| sample_from_s_eta(eta, L + K, N, Q))
        .collect();

    // println!("sn: {:?}", sn);

    let tn = multiply_polynomial_matrix_vector(&a_bar, &sn, &Q);
    // println!("tn: {:?}", tn);

    let t_sum = sum_tn_matrices(&tn, &Q);
    // println!("t_sum: {:?}", t_sum);

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

    let pk = (a_sum.clone(), t_sum.clone());
    let pk_copy = pk.clone();
    // println!("Local output for Pn: {:?}", (skn, pk));

    let message = "example_message";
    let ck_limit = 5;

    let ck = h3(message, &pk_copy, &ck_limit);
    println!("Per-message commitment key ck: {}", ck);

    let f64_party_number = party_number as f64;

    let alpha: f64 = 11.0 * f64_party_number * 15.0;
    let kappa_usize = 60;
    let gamma: f64 = 1.1;
    let t: f64 = 12.0;
    let epsilon: f64 = 0.1;
    let n: f64 = 256.0;
    let l: f64 = 2.0;
    let k: f64 = 1.0;
    let kappa: f64 = kappa_usize as f64;

    let large_t = kappa * eta_clone * (n * (l + k)).sqrt();
    println!("large_t: {}", large_t);
    let sigma = &alpha * &large_t;
    println!("sigma: {}", sigma);
    let sampler = GaussianSampler::new(sigma);
    let large_b = gamma * sigma * (n * (l + k)).sqrt();

    let m_f64 = ((t / alpha) + (1.0 / (2.0 * alpha.powi(2)))).exp();
    println!("M: {}", m_f64);
    let mn = m_f64.powf(f64_party_number);
    println!("M^n: {}", mn);

    let trapq_candidate = n.powf(2.0 + epsilon);
    let trapq = next_prime(trapq_candidate.to_u64().unwrap());

    let trapl = trapq.to_f64().unwrap().log2().ceil() as usize;
    let trapw = trapq.to_f64().unwrap().log2().ceil() as usize;
    let s = &alpha * &large_t * (2.0 * std::f64::consts::PI).sqrt();

    println!("trapl: {}, trapw: {}, s: {}", trapl, trapw, s);

    let party_number = party_number as usize;

    let mut last_rejec_zn_result: Option<Vec<Vec<Polynomial>>> = None;
    let mut last_derived_challenge: Option<Polynomial> = None;
    let mut sampled_rn: Vec<Polynomial> = Vec::new();
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

        let k = K;
        sampled_rn = samplern(party_number, trapl, trapw, eta_clone, Q);
        // println!("sampled_rn: {:?}", sampled_rn);

        ahat = c_gen(&sampler, Q, trapl, trapw);
        // println!("ahat: {:?}", ahat);

        let result = commitck(&wn, &sampled_rn, &ahat, party_number as usize);
        let (zero, comn) = result;
        comn_per_party = comn;
        // let rows = comn_per_party.len();
        // let cols = comn_per_party[0].len();
        // println!("com_per_party: {:?}", comn_per_party);
        // println!("com_per_party has {} rows and {} columns.", rows, cols);

        com = setcom(comn_per_party.clone(), K);
        // println!("Commitment com: {:?}", com);

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
                println!("rejec_zn_result has {} rows and {} columns.", rows, cols);
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
            let (sign_zn, sign_rn) = compute_signature(&rejec_zn_result, &sampled_rn);
            let ver_w = ready_verification(
                &a_bar,
                derived_challenge,
                &pk_copy,
                &kappa_usize,
                &Q,
                &sign_zn,
                &com,
                &message,
                &ck_limit,
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

struct TableSampler {
    values: Arc<Vec<i128>>, // 値をi128型で保持
    dist: Uniform<usize>,   // 等確率でのインデックス抽出
    rng: Mutex<ThreadRng>,  // ランダム数生成器
}

impl TableSampler {
    fn new(sigma: i128) -> Self {
        let range = (sigma * 6) as i128; // f64からi128への型変換を明示
        let values: Vec<i128> = (-range..=range).collect(); // f64からi128への範囲生成
        let dist = Uniform::new(0, values.len());
        let rng = Mutex::new(thread_rng());
        Self {
            values: Arc::new(values),
            dist,
            rng,
        }
    }

    fn sample(&self) -> i128 {
        let mut rng = self.rng.lock().unwrap();
        let index = self.dist.sample(&mut *rng);
        let sampled_value = self.values[index]; // 直接i128値を返す
        sampled_value
    }
}

fn gaussian_sample_polynomial_fromtable(sampler: &TableSampler, q: i128) -> Polynomial {
    let coeffs: Vec<i128> = (0..N)
        .map(|_| {
            let sample = sampler.sample();
            (sample + q) % q // 負のサンプルを適切に扱い、qモジュロを行います。
        })
        .collect();

    Polynomial::new(coeffs, q)
}

fn generate_random_matrix_fromtable(
    k: usize,
    l: usize,
    sampler: &TableSampler,
    q: i128,
    party_number: usize,
) -> Vec<Vec<Polynomial>> {
    let mut matrices: Vec<Vec<Polynomial>> = Vec::with_capacity(party_number);
    for _ in 0..party_number {
        let matrix: Vec<Polynomial> = (0..k * l)
            .map(|_| gaussian_sample_polynomial_fromtable(sampler, q))
            .collect();
        matrices.push(matrix);
    }
    matrices
}

// ガウスサンプルに基づいて多項式を生成する関数
fn gaussian_sample_polynomial(sampler: &GaussianSampler, q: i128) -> Polynomial {
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
fn generate_random_matrix(
    k: usize,
    l: usize,
    sampler: &GaussianSampler,
    q: i128,
    party_number: usize,
) -> Vec<Vec<Polynomial>> {
    let mut matrices: Vec<Vec<Polynomial>> = Vec::with_capacity(party_number);
    for _ in 0..party_number {
        let matrix: Vec<Polynomial> = (0..k * l)
            .map(|_| gaussian_sample_polynomial(sampler, q))
            .collect();
        matrices.push(matrix);
    }
    matrices
}

//可逆な1*1行列を返す関数
fn generate_invertible_matrix(sampler: &GaussianSampler, q: i128) -> Vec<Vec<Polynomial>> {
    loop {
        let ahat1_1: Vec<Vec<Polynomial>> = vec![vec![gaussian_sample_polynomial(&sampler, q)]];
        // ここでは、多項式が0でないことを確認することで「可逆」と仮定
        if !ahat1_1[0][0].coeffs[0].is_zero() {
            return ahat1_1;
        }
    }
}

// 行列とベクトルの乗算を行う関数
fn multiply_polynomial_matrix_vector(
    a_bar: &[Vec<Polynomial>],
    sn: &[Vec<Polynomial>],
    q: &i128,
) -> Vec<Vec<Polynomial>> {
    let p = sn.len(); // snの行数（列数ではないことに注意）
    let mut result = Vec::with_capacity(p);

    // 各snの行に対して計算を行う
    for column in 0..p {
        let mut column_result = Vec::new();

        // a_bar の各行に対する計算を行います
        for a_bar_row in a_bar.iter() {
            let mut result_poly = Polynomial::new(vec![0; a_bar_row[0].coeffs.len()], *q);

            // a_barの行とsnの特定の列の要素ごとの乗算と加算
            for (a_poly, s_poly) in a_bar_row.iter().zip(&sn[column]) {
                let product = a_poly.mul_ntt(s_poly);
                // println!("product: {:?}", product);
                // let product_lifted = polynomial_to_f64_vec(&product);
                // let calculate_norm = calculate_norm(&product_lifted);
                // println!("calculate_norm: {:?}", calculate_norm);
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

// ランダムオラクルH3関数
fn h3(message: &str, public_key: &(Vec<Polynomial>, Vec<Polynomial>), ck_limit: &i32) -> BigInt {
    let mut combined = String::new();
    write!(&mut combined, "{}", message).expect("Failed to write message to string");

    for poly in &public_key.0 {
        write!(&mut combined, "{}", poly.to_string())
            .expect("Failed to write polynomial to string");
    }

    for poly in &public_key.1 {
        write!(&mut combined, "{}", poly.to_string())
            .expect("Failed to write polynomial to string");
    }

    let mut hasher = Sha256::new();
    hasher.update(combined.as_bytes());
    let hash_output = hasher.finalize();

    let hash_int = BigInt::from_bytes_be(Sign::Plus, &hash_output);
    let two_pow_256 = BigInt::from(2).pow(256);
    let scale_factor = BigInt::from(2 * ck_limit) * &two_pow_256 / (&two_pow_256 - BigInt::one());
    let scaled_value = (hash_int * scale_factor / &two_pow_256) - BigInt::from(ck_limit.clone());

    scaled_value
}

// 素数判定関数
fn is_prime(n: u64) -> bool {
    if n <= 1 {
        return false;
    }
    if n <= 3 {
        return true;
    }
    if n % 2 == 0 || n % 3 == 0 {
        return false;
    }
    let mut i: u64 = 5;
    while i * i <= n {
        if n % i == 0 || n % (i + 2) == 0 {
            return false;
        }
        i += 6;
    }
    true
}

// 次の素数を見つける関数
fn next_prime(n: u64) -> u64 {
    let mut candidate = n + 1;
    while !is_prime(candidate) {
        candidate += 1;
    }
    candidate
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
                .map(|_| gaussian_sample_polynomial(&sampler, q))
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

// rの範囲内で整数をサンプリングする関数
fn sample_from_s_r(size: f64) -> i128 {
    let mut rng = thread_rng();
    let normal = Normal::new(0.0, size).expect("Failed to create normal distribution");
    let sampled_value = normal.sample(&mut rng);
    sampled_value.round() as i128 // f64の値を四捨五入してi128型にキャスト
}

// Polynomialのベクターを生成する関数
fn samplern(
    party_number: usize,
    trapl: usize,
    trapw: usize,
    eta: f64,
    mod_val: i128,
) -> Vec<Polynomial> {
    let mut sampled_rn = Vec::new();
    for _ in 0..party_number {
        let mut polynomial_coeffs = Vec::new();
        for _ in 0..(trapl + 2 * trapw) {
            let sampled_value = sample_from_s_r(eta);
            polynomial_coeffs.push(sampled_value % mod_val); // サンプリングされた値をmod_valで剰余
        }
        let polynomial = Polynomial::new(polynomial_coeffs, mod_val);
        sampled_rn.push(polynomial);
    }
    sampled_rn
}

// CGen関数のRust実装
fn c_gen(sampler: &GaussianSampler, q: i128, trapl: usize, trapw: usize) -> Vec<Vec<Polynomial>> {
    let ahat1_1 = generate_invertible_matrix(sampler, q);
    let mut ahat1_j = generate_random_matrix(1, trapl + 2 * trapw - 1, sampler, q, 1)[0].clone();

    // ahat1_1を最初の列に、ahat1_jをその後ろに追加して1行目を作成
    let mut first_row = Vec::new();
    first_row.push(ahat1_1[0][0].clone()); // ahat1_1の最初の要素を追加
    first_row.append(&mut ahat1_j); // ahat1_jの要素を追加

    let list1 = vec![
        Polynomial::new(vec![0], q.clone()),
        Polynomial::new(vec![1], q.clone()),
    ];
    let mut ahat2_j = generate_random_matrix(1, trapl + 2 * trapw - 2, sampler, q, 1)[0].clone();

    // list1とahat2_jを結合して2行目を作成
    let mut second_row = list1;
    second_row.append(&mut ahat2_j); // ahat2_jの要素を追加

    // 1行目と2行目を結合して最終的な行列ahatを作成
    vec![first_row, second_row]
}

fn commitck(
    flat_wn: &Vec<Vec<Polynomial>>,
    sampled_rn: &Vec<Polynomial>,
    ahat: &Vec<Vec<Polynomial>>,
    party_number: usize,
) -> (Vec<Vec<Polynomial>>, Vec<Vec<Vec<Polynomial>>>) {
    let mut comn_per_party = vec![Vec::new(); party_number]; // Vec<Vec<Vec<Polynomial>>>

    // `flat_wn` のサブリストごとに `sampled_rn` の対応する要素を使用
    for (p, temp_wn) in flat_wn.iter().enumerate() {
        let sampled_poly = &sampled_rn[p]; // `p` は `flat_wn` のサブリストのインデックスに対応
                                           // println!("sampled_poly: {:?}", sampled_poly);

        for poly in temp_wn.iter() {
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
            // println!("f: {:?}", f);

            let party_index = p % party_number;
            comn_per_party[party_index].extend(f); // 合計された結果をパーティに格納
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
        // 各行の計算結果を保持するための新しい多項式を初期化
        let mut sum_poly = Polynomial::new(vec![0], sampled_poly.mod_val.clone());

        // ahat_rowの各多項式とsampled_polyの各係数を乗算して加算する
        for (ahat_poly, coeff) in ahat_row.iter().zip(sampled_poly.coeffs.iter()) {
            let mut product_poly = ahat_poly.clone();
            // ahat_polyの各係数にsampled_polyの係数を乗算して新しい多項式を生成
            for p in product_poly.coeffs.iter_mut() {
                *p *= coeff;
                *p %= &sampled_poly.mod_val; // mod_valによる剰余を取る
            }
            // product_poly.normalize();  // 正規化
            sum_poly = sum_poly.add_ref(&product_poly); // 加算
        }
        // sum_poly.normalize();  // 最終的な多項式の正規化
        result.push(vec![sum_poly]); // 各行の計算結果をresultに追加
    }
    result
}

//a. set com
// comn_per_partyから合計コミットメントを計算する関数
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

    // 結果を一次元のリストではなく、二次元のリストに格納するために初期化方法を変更
    let mut grouped_results = vec![Vec::new(); num_rows / k]; // k個ずつグループ化するための二次元ベクター

    // 一時的な結果を格納するためのフラットなリストを作成
    let mut temp_results = vec![vec![Polynomial::new(vec![0], Q); num_cols]; num_rows];

    // 入力データの全ての要素を足し合わせる
    for party_coms in comn_per_party {
        for (i, row_coms) in party_coms.iter().enumerate() {
            for (j, com) in row_coms.iter().enumerate() {
                temp_results[i][j] = temp_results[i][j].add_ref(com);
            }
        }
    }

    // 一次元の結果を二次元のグループに分ける
    for (i, result) in temp_results.iter().enumerate() {
        let group_index = i / k; // k要素ごとに同じグループに配置
        grouped_results[group_index].push(result.clone()); // 各グループに結果を追加
    }

    grouped_results
}

//b. derive challenge
// h0関数の更新版
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
    let mut rejec_zn_results = Vec::new();

    // 外側のベクトル（パーティごとのリスト）に対してループ
    for (csn_party, zn_party) in csn_list.iter().zip(zn_list.iter()) {
        let mut rejec_zn_party_result = Vec::new();

        let mut rohs_rms = Vec::new();
        let mut rohcsn_s_rms = Vec::new();
        let mut sum_rohs_rm = 0.0;
        let mut sum_rohcsn_s_rm = 0.0;
        
        // 各多項式に対してガウス分布の分母を求める計算を行う
        for (csn_poly, zn_poly) in csn_party.iter().zip(zn_party.iter()) {
            let zn_lifted = polynomial_to_f64_vec(zn_poly);
            // println!("zn_lifted: {:?}", zn_lifted);
            let csn_lifted = polynomial_to_f64_vec(csn_poly);

            let (rohs_rm, rohcsn_s_rm) = calculate_sums_for_poly(&csn_lifted, &zn_lifted, s);
            // println!("rohs_rm: {}", rohs_rm);
            // println!("rohcsn_s_rm: {}", rohcsn_s_rm);
            rohs_rms.push(rohs_rm);
            rohcsn_s_rms.push(rohcsn_s_rm);

            sum_rohs_rm += rohs_rm;
            sum_rohcsn_s_rm += rohcsn_s_rm;
        }

        // 各多項式に対して拒否サンプリングを実行
        for ((rohs_rm, rohcsn_s_rm), zn_poly) in rohs_rms.iter().zip(rohcsn_s_rms.iter()).zip(zn_party.iter()) {
            // println!("rohs_rm: {}", rohs_rm);
            // println!("sum_rohs_rm: {}", sum_rohs_rm);
            // println!("rohcsn_s_rm: {}", rohcsn_s_rm);
            // println!("sum_rohcsn_s_rm: {}", sum_rohcsn_s_rm);
            // println!("{}", rohs_rm / sum_rohs_rm);
            // println!("{}", m * (rohcsn_s_rm / sum_rohcsn_s_rm));
            let ratio = (rohs_rm / sum_rohs_rm) / (m* (rohcsn_s_rm / sum_rohcsn_s_rm));
            println!("Ratio: {}", ratio);

            // 比率と1の小さい方を選ぶ
            let acceptance_probability = ratio.min(1.0);
            let random_probability: f64 = rand::random();

            // ランダムな確率を使用してサンプルを受け入れるか拒否するかを決定
            if random_probability <= acceptance_probability {
                rejec_zn_party_result.push(zn_poly.clone());
            } else {
                // 拒否された場合は再サンプリングが必要
                return Err("restart");
            }
        }

        rejec_zn_results.push(rejec_zn_party_result);
    }
    // println!("rejec_zn_results: {:?}", rejec_zn_results);

    Ok(rejec_zn_results)
}

// 単一の多項式のための比率計算関数
fn calculate_sums_for_poly(csn: &Vec<f64>, zn: &Vec<f64>, s: f64) -> (f64, f64) {
    let zn_norm = calculate_norm(zn);
    let csn_minus_zn = sub_ref_f64(zn, csn);
    let csn_norm = calculate_norm(&csn_minus_zn);
    println!("zn_norm: {}", zn_norm);
    // println!("csn_norm: {}", csn_norm);
    println!("s: {}", s);

    let rohs_rm = ((-PI * zn_norm.powi(2)) / (s.powi(2))).exp();
    let rohcsn_s_rm = ((-PI * csn_norm.powi(2)) / (s.powi(2))).exp();

    (rohs_rm, rohcsn_s_rm)
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
    //println!("zn_result: {:?}", zn_result);
    for zn_party in zn_result {
        // 各パーティの多項式ベクトルを一つの大きなベクトルに結合
        let combined_coeffs: Vec<f64> = zn_party
            .iter()
            .flat_map(|poly| polynomial_to_f64_vec(poly))
            .collect();

        // 結合されたベクトルのノルムを計算
        let zn_norm = calculate_norm(&combined_coeffs);
        println!("Combined zn_norm: {}", zn_norm);
        println!("large_b: {}", large_b);

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
                    // product.normalize();
                    product
                })
                .collect()
        })
        .collect();
    // let recon_wn_rights: Vec<Vec<Polynomial>> = multiply_polynomial_matrix_vector(a_bar, csn, q);
    // println!("recon_wn_rights: {:?}", recon_wn_rights);

    //a_barとznの乗算を行い，その結果を保存
    let addition_result = multiply_polynomial_matrix_vector(a_bar, zn, q);

    // 最終的な結果として addition_result から recon_wn_rights を減算
    for (addition_row, recon_wn_right_row) in addition_result.iter().zip(recon_wn_rights.iter()) {
        let reconted_row: Vec<Polynomial> = addition_row
            .iter()
            .zip(recon_wn_right_row)
            .map(|(addition_poly, recon_wn_right_poly)| {
                let mut result = addition_poly.clone().sub(recon_wn_right_poly.clone());
                // result.normalize();
                result
            })
            .collect();
        reconted_wj.push(reconted_row);
    }

    reconted_wj
}

fn validate_openck(
    sampled_rn: &Vec<Polynomial>,
    reconted_wj: &Vec<Vec<Polynomial>>,
    comn_per_party: &Vec<Vec<Vec<Polynomial>>>,
    large_b: f64,
    ahat: &Vec<Vec<Polynomial>>,
    k: usize, // グループサイズ k をパラメータとして追加
) -> String {
    let mut poly_index = 0; // 全体のポリノミアルインデックスを追跡する変数

    for (j, temp_reconted_wj) in reconted_wj.iter().enumerate() {
        let sampled_poly = &sampled_rn[j]; // サブリストに対応する sampled_rn の要素を取得

        for _poly in temp_reconted_wj.iter() {
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

// fleftのフォーマットを変更して、余分なネストを避ける
fn format_openck_fleft(openck_fleft: Vec<Vec<Polynomial>>) -> Vec<Vec<Vec<Polynomial>>> {
    vec![openck_fleft] // これにより、Vec<Vec<Polynomial>> を Vec<Vec<Vec<Polynomial>>> に変換
}

// 二つの多層行列を加算し、フラットな行列（Vec<Vec<Polynomial>>）を返す関数の修正
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
    sampled_rn: &Vec<Polynomial>,
) -> (Vec<Polynomial>, Vec<Polynomial>) {
    let sign_zn = sum_polynomials_by_index(rejec_zn_result);
    let sign_rn = sum_polynomials(sampled_rn); // 修正: 単一の多項式のリストを合計する

    (sign_zn, vec![sign_rn]) // 修正: 結果をベクトル形式で返す
}

// 各インデックスの多項式を加算する関数
fn sum_polynomials_by_index(sampled_rn: &Vec<Vec<Polynomial>>) -> Vec<Polynomial> {
    if sampled_rn.is_empty() {
        return Vec::new();
    }

    let num_polynomials = sampled_rn[0].len(); // 各パーティーが持つ多項式の数
    let mut sum_polynomials =
        vec![Polynomial::new(vec![], sampled_rn[0][0].mod_val.clone()); num_polynomials];

    for party_polynomials in sampled_rn {
        for (index, poly) in party_polynomials.iter().enumerate() {
            sum_polynomials[index] = sum_polynomials[index].add_ref(poly);
        }
    }

    sum_polynomials
}

fn sum_polynomials(sampled_rn: &Vec<Polynomial>) -> Polynomial {
    // 初期多項式を設定（mod_valを適切に設定するため、sampled_rnの最初の要素から借用）
    let mut total_sum = Polynomial::new(vec![0], sampled_rn[0].mod_val.clone());

    // 全ての多項式を合計する
    for poly in sampled_rn.iter() {
        total_sum = total_sum.add_ref(poly); // 多項式を足し合わせる
    }

    total_sum
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
    ck_limit: &i32,
    t_sum: &Vec<Polynomial>,
) -> Vec<Polynomial> {


    // commitment_keyの計算
    let ready_ck = h3(message, &pk, ck_limit);
    println!("ready_ck: {:?}", ready_ck);


    // challengeの計算
    let ready_derived_challenge = h0(&com, message, &pk, N, kappa, &Q);
    println!("ready_derived_challenge: {:?}", ready_derived_challenge);

    // a_bar とsign_znの乗算
    let ready_w_left: Vec<Polynomial> = multiply_polynomial_matrix_with_vector(a_bar, sign_zn, q);

    // challengeとt_sumの乗算
    let recon_wn_right: Vec<Polynomial> = t_sum
        .iter()
        .map(|tsum_poly| {
            let mut product = challenge.clone().mul_ntt(tsum_poly);
            // product.normalize();
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
    b: f64,
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

        println!("b: {}", b);
        println!("sign_rn_norms: {:?}", sign_rn_norms[0]);

        // com[j] と each_openck_result を比較
        if sign_rn_norms[0] <= b && com[j] == each_openck_result {
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
    // ここにmatrix1とmatrix2を加算するロジックを実装
    // この例では、単純な要素ごとの加算を行いますが、実際にはサイズのチェックなどが必要になる場合があります
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
    println!("Norm of sign_zn: {}", zn_norm[0]);
    let bn = (party_number as f64).sqrt() * b;
    println!("Threshold bn for party {}", bn);

    let mut verification_failed = false;

    for i in 0..party_number {
        if zn_norm[0] > bn || eachparty_openck(sign_rn, ver_w, com, ahat, b, K).is_err() {
            println!("Verification is invalid for party {}", i);
            verification_failed = true;
            break;
        }
    }

    if !verification_failed {
        println!("All verifications are valid.");
    }
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
