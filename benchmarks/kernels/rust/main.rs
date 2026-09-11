// The Rust side of the kernel comparison (benchmarks/kernels/README.md): the
// same command line, data, and output as the Oak runner, standard library
// only, each algorithm written plainly: a word-at-a-time SHA-256, a
// table-driven CRC-32C, and the loops.
use std::time::Instant;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

fn compress(h: &mut [u32; 8], block: &[u8]) {
    let mut w = [0u32; 64];
    for i in 0..16 {
        w[i] = u32::from_be_bytes([block[4 * i], block[4 * i + 1], block[4 * i + 2], block[4 * i + 3]]);
    }
    for i in 16..64 {
        let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
        let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
    }
    let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh) = (h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7]);
    for i in 0..64 {
        let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let ch = (e & f) ^ (!e & g);
        let t1 = hh.wrapping_add(s1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]);
        let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let t2 = s0.wrapping_add(maj);
        hh = g; g = f; f = e; e = d.wrapping_add(t1); d = c; c = b; b = a; a = t1.wrapping_add(t2);
    }
    h[0] = h[0].wrapping_add(a); h[1] = h[1].wrapping_add(b); h[2] = h[2].wrapping_add(c); h[3] = h[3].wrapping_add(d);
    h[4] = h[4].wrapping_add(e); h[5] = h[5].wrapping_add(f); h[6] = h[6].wrapping_add(g); h[7] = h[7].wrapping_add(hh);
}

fn sha256(data: &[u8], out: &mut [u8; 32]) {
    let mut h: [u32; 8] = [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];
    let n = data.len();
    let mut i = 0;
    while i + 64 <= n {
        compress(&mut h, &data[i..i + 64]);
        i += 64;
    }
    let mut tail = [0u8; 128];
    let rest = n - i;
    tail[..rest].copy_from_slice(&data[i..]);
    tail[rest] = 0x80;
    let padded = if rest + 1 > 56 { 128 } else { 64 };
    tail[padded - 8..padded].copy_from_slice(&((n as u64) * 8).to_be_bytes());
    let mut j = 0;
    while j < padded {
        compress(&mut h, &tail[j..j + 64]);
        j += 64;
    }
    for j in 0..8 {
        out[4 * j..4 * j + 4].copy_from_slice(&h[j].to_be_bytes());
    }
}

fn crc_table() -> [u32; 256] {
    let mut table = [0u32; 256];
    for i in 0..256u32 {
        let mut c = i;
        for _ in 0..8 {
            c = if c & 1 != 0 { (c >> 1) ^ 0x82f63b78 } else { c >> 1 };
        }
        table[i as usize] = c;
    }
    table
}

fn crc32c(table: &[u32; 256], data: &[u8]) -> u32 {
    let mut c = !0u32;
    for &b in data {
        c = table[((c as u8) ^ b) as usize] ^ (c >> 8);
    }
    !c
}

fn dot(a: &[f32], b: &[f32]) -> f32 {
    let mut total = 0.0f32;
    for i in 0..a.len() {
        total += a[i] * b[i];
    }
    total
}

fn sum(v: &[u64]) -> u64 {
    let mut total = 0u64;
    for &x in v {
        total = total.wrapping_add(x);
    }
    total
}

fn search(keys: &[u64], probes: &[u64]) -> u32 {
    let mut hits = 0u32;
    for &target in probes {
        let (mut lo, mut hi) = (0usize, keys.len());
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if keys[mid] == target { hits += 1; break; } else if keys[mid] < target { lo = mid + 1; } else { hi = mid; }
        }
    }
    hits
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 5 { eprintln!("usage: kernels KERNEL SIZE ROUNDS SAMPLES"); std::process::exit(2); }
    let kernel = args[1].as_str();
    let size: usize = args[2].parse().unwrap();
    let rounds: usize = args[3].parse().unwrap();
    let samples: usize = args[4].parse().unwrap();
    let mut rng = Rng(0x9E3779B97F4A7C15);
    let mut bytes = vec![0u8; size];
    let mut fa = vec![0f32; size];
    let mut fb = vec![0f32; size];
    let mut words = vec![0u64; size];
    let probe_count = if size / 16 == 0 { 1 } else { size / 16 };
    let mut probes = vec![0u64; probe_count];
    for i in 0..size {
        let r = rng.next();
        bytes[i] = r as u8;
        fa[i] = (r & 0xFFFF) as f32 / 65536.0;
        fb[i] = ((r >> 16) & 0xFFFF) as f32 / 65536.0;
        words[i] = (i as u64) * 3;
    }
    for i in 0..probe_count { probes[i] = rng.next() % ((size as u64) * 3 + 3); }
    let table = crc_table();
    let mut out = [0u8; 32];
    let mut width = 4;
    let mut ns = vec![0f64; samples];
    for s in 0..samples {
        let start = Instant::now();
        let mut sink = 0u64;
        for _ in 0..rounds {
            match kernel {
                "sha256" => { width = 32; sha256(&bytes, &mut out); sink = sink.wrapping_add(out[0] as u64); }
                "crc32c" => { let c = crc32c(&table, &bytes); out[..4].copy_from_slice(&c.to_le_bytes()); sink = sink.wrapping_add(c as u64); }
                "dot" => { let d = dot(&fa, &fb); out[..4].copy_from_slice(&d.to_bits().to_le_bytes()); sink = sink.wrapping_add(out[0] as u64); }
                "sum" => { width = 8; let t = sum(&words); out[..8].copy_from_slice(&t.to_le_bytes()); sink = sink.wrapping_add(t); }
                "search" => { let h = search(&words, &probes); out[..4].copy_from_slice(&h.to_le_bytes()); sink = sink.wrapping_add(h as u64); }
                _ => { eprintln!("unknown kernel {}", kernel); std::process::exit(2); }
            }
        }
        ns[s] = start.elapsed().as_nanos() as f64 / rounds as f64;
        if sink == u64::MAX { eprintln!("sink"); }
    }
    ns.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let checksum: String = out[..width].iter().map(|b| format!("{:02x}", b)).collect();
    print!("{{\"impl\":\"rust\",\"kernel\":\"{}\",\"size\":{},\"checksum\":\"{}\",\"ns_per_op_median\":{:.1},\"samples\":[", kernel, size, checksum, ns[samples / 2]);
    for (i, v) in ns.iter().enumerate() { if i > 0 { print!(","); } print!("{:.1}", v); }
    println!("]}}");
}
