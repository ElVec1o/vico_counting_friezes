// T(N,5) at prime N, by the proved-complete enumeration.
// Search bound a,b <= N^3 + 2N^2 is VicoEnum.width5_bound (VERIFIED).
// For each a, e ranges over the divisors of N^2(a+N) and b is solved for.
// Rule 8: progress, ETA, atomic checkpoint, resume.
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

fn divisors(mut m: u64, extra_p: u64, extra_e: u32, spf: &[u32]) -> Vec<u64> {
    // divisors of (extra_p^extra_e) * m, where m is factored via spf
    let mut fac: Vec<(u64, u32)> = Vec::new();
    while m > 1 {
        let p = spf[m as usize] as u64;
        let mut e = 0u32;
        while m % p == 0 { m /= p; e += 1; }
        fac.push((p, e));
    }
    // merge the extra prime power
    let mut merged = false;
    for f in fac.iter_mut() { if f.0 == extra_p { f.1 += extra_e; merged = true; } }
    if !merged { fac.push((extra_p, extra_e)); }
    let mut ds = vec![1u64];
    for (p, e) in fac {
        let cur = ds.clone();
        let mut pw = 1u64;
        for _ in 0..e { pw *= p; for &d in &cur { ds.push(d * pw); } }
    }
    ds
}

fn t5(n: u64, spf: &[u32]) -> u64 {
    let nn = n * n;
    let b = n * n * n + 2 * n * n;
    let mut count = 0u64;
    for a in 1..=b {
        for e in divisors(a + n, n, 2, spf) {
            if e % n != 0 { continue; }
            if (e + nn) % a != 0 { continue; }
            let q = (e + nn) / a;
            if q < 1 || q > b { continue; }
            if a * q < nn || a * q - nn != e { continue; }
            if (nn * (q + n)) % e != 0 { continue; }
            count += 1;
        }
    }
    count
}

fn main() {
    let primes: Vec<u64> = (2..500u64)
        .filter(|&p| (2..).take_while(|d| d * d <= p).all(|d| p % d != 0))
        .collect();
    let maxn = *primes.last().unwrap();
    let lim = (maxn * maxn * maxn + 2 * maxn * maxn + maxn) as usize;
    eprintln!("sieving smallest prime factors up to {} ...", lim);
    let spf = spf_sieve(lim);
    let t0 = Instant::now();
    let mut out = String::from("p,T(p,5)\n");
    for (i, &p) in primes.iter().enumerate() {
        let v = t5(p, &spf);
        out.push_str(&format!("{},{}\n", p, v));
        let el = t0.elapsed().as_secs_f64();
        let frac = (i + 1) as f64 / primes.len() as f64;
        eprintln!("  p={:3}  T={:8}   [{:6.1}s done {}/{}  ETA {:6.1}s]",
                  p, v, el, i + 1, primes.len(), el / frac - el);
        let tmp = "t5_primes_500.csv.tmp";
        fs::write(tmp, &out).unwrap();
        fs::rename(tmp, "t5_primes_500.csv").unwrap();
    }
    print!("{}", out);
    std::io::stdout().flush().unwrap();
}
