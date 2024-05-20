mod main; // もし main.rs に関数がある場合
use main::main_function;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

fn benchmark_main(c: &mut Criterion) {
    let mut group = c.benchmark_group("Main Function Benchmarks");
    group.sample_size(10); // サンプルサイズを10に設定
    for party_number in &[2, 10, 50, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000] {
        group.bench_with_input(BenchmarkId::new("main_function", party_number), party_number, |b, &party_number| {
            b.iter(|| {
                main_function(party_number);
            });
        });
    }
    group.finish();
}

criterion_group!(benches, benchmark_main);
criterion_main!(benches);
