// T(N,5) over a long range, via the g-free reduction.
//
//   T(N,5) = #{(u,v,M) : gcd(u,v)=1, M | N^2, uv | N(u+v)+M, N uv | M(N(u+v)+M)}
//
// with the PROVED bound min(u,v) < 3N (VicoEnum.t5_min_bound) and v | Nu+M
// (VicoEnum.t5_large_dvd), so the sweep runs u < 3N and v over divisors of Nu+M.
// Ordered pairs are recovered by counting u < v twice (VicoEnum.t5_order_inj).
//
// Purpose: decide whether T(N,5) >= cN can hold. Rule 8: progress, ETA, atomic
// checkpoint, resume.
use std::fs;
use std::io::Write;
use std::time::Instant;

fn spf_sieve(n: usize) -> Vec<u32> {
    let mut s: Vec<u32> = (0..=n).map(|i| i as u32).collect();
    let mut i = 2usize;
    while i * i <= n {
        if s[i] == i as u32 {
            let mut j = i * i;
            while j <= n { if s[j] == j as u32 { s[j] = i as u32; } j += i; }
            }
        i += 1;
    }
    s
}

fn divisors(mut n: usize, spf: &[u32]) -> Vec<i64> {
    let mut ds: Vec<i64> = vec![1];
    while n > 1 {
        let p = spf[n] as usize;
        let mut k = 0;
        while n % p == 0 { n /= p; k += 1; }
        let len = ds.len();
        let mut pw: i64 = 1;
        for _ in 0..k {
            pw *= p as i64;
            for i in 0..len { let d = ds[i] * pw; ds.push(d); }
        }
    }
    ds
}

fn gcd(a: i64, b: i64) -> i64 { if b == 0 { a } else { gcd(b, a % b) } }

fn t5(n: i64, spf: &[u32]) -> i64 {
    let nn = n * n;
    let dm = divisors(nn as usize, spf);
    let mut total: i64 = 0;
    for &m in &dm {
        for u in 1..(3 * n) {
            let target = n * u + m;
            for &v in divisors(target as usize, spf).iter() {
                if v < u { continue; }
                if gcd(u, v) != 1 { continue; }
                let s = n * (u + v) + m;
                if s % (u * v) != 0 { continue; }
                if (m % (n * u * v)) != 0 && (m * s) % (n * u * v) != 0 { continue; }
                total += if u == v { 1 } else { 2 };
            }
        }
    }
    total
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let hi: i64 = args.get(1).map(|s| s.parse().unwrap()).unwrap_or(600);
    let path = "../data/T5_growth.csv";
    let tmp = "../data/T5_growth.csv.tmp";

    let mut rows: Vec<(i64, i64)> = Vec::new();
    let mut start: i64 = 1;
    if let Ok(txt) = fs::read_to_string(path) {
        for line in txt.lines().skip(1) {
            let p: Vec<&str> = line.split(',').collect();
            if p.len() == 2 {
                if let (Ok(a), Ok(b)) = (p[0].parse::<i64>(), p[1].parse::<i64>()) {
                    rows.push((a, b));
                    start = a + 1;
                }
            }
        }
        eprintln!("resumed at N = {}", start);
    }

    let spf = spf_sieve((4 * hi * hi + 10) as usize);
    let t0 = Instant::now();
    let mut worst = f64::INFINITY;
    let mut worst_n = 0i64;
    for n in start..=hi {
        let t = t5(n, &spf);
        rows.push((n, t));
        let r = t as f64 / n as f64;
        if r < worst { worst = r; worst_n = n; }
        if n % 25 == 0 || n == hi {
            let done = (n - start + 1) as f64;
            let tot = (hi - start + 1) as f64;
            let el = t0.elapsed().as_secs_f64();
            let eta = if done > 0.0 { el * (tot - done) / done } else { 0.0 };
            eprintln!("N={:4}/{}  T={:8}  T/N={:7.3}   min T/N so far {:.4} at N={}   \
                       {:.0}s elapsed, ETA {:.0}s", n, hi, t, r, worst, worst_n, el, eta);
            let mut f = fs::File::create(tmp).unwrap();
            writeln!(f, "N,\"T(N,5)\"").unwrap();
            for (a, b) in &rows { writeln!(f, "{},{}", a, b).unwrap(); }
            f.sync_all().unwrap();
            fs::rename(tmp, path).unwrap();
        }
    }
    eprintln!("done. min T/N = {:.4} at N = {}", worst, worst_n);
}
