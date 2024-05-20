// //　共有データ構造の定義
// pub struct KeygenOutput {
//     pub a_n: Vec<Vec<Polynomial>>, // 公開行列A_n
//     pub gn: Vec<String>, // ランダムオラクルコミットメントg_n
//     pub a_sum: Vec<Polynomial>, // 行列A_nの合計
//     pub a_bar: Vec<Vec<Polynomial>>, // 結合行列A_bar
//     pub sn: Vec<Array1<i32>>, // 秘密鍵sn
//     pub tn: Vec<Array2<i32>>, // 変換行列Tn
//     pub t_sum: Array2<i32>, // Tnの合計
//     pub g_prime_n: Vec<String>, // コミットメントg'_n
// }

// // 必要に応じてPolynomial構造体も共有モジュールに移動させる
// #[derive(Clone, Debug)]
// pub struct Polynomial {
//     pub coeffs: Vec<BigUint>,
//     pub mod_val: BigUint,
// }
