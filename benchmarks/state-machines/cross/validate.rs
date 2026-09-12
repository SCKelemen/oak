// Rust standard library: std::str::from_utf8 over the shared input.
use std::time::Instant;
fn main() {
    let buf = std::fs::read("input.bin").expect("run gen_input first");
    let mut best = f64::MAX;
    let mut ok = false;
    for _ in 0..5 {
        let t0 = Instant::now();
        ok = std::str::from_utf8(&buf).is_ok();
        let t = t0.elapsed().as_nanos() as f64;
        if t < best { best = t; }
    }
    let n = buf.len() as f64;
    println!("{:<34} {:6.2} ns/byte  {:6.2} GB/s", "Rust std::str::from_utf8", best / n, n / best);
    if !ok { std::process::exit(1); }
}
