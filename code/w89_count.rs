// Complete enumeration at widths 8 and 9 over the proved Cuntz-Holm box.
//
// Free parameters p_0..p_{n-4}, each at most (n-4)N^3 + 2N^2 (Theorem thm:uniform).
// DFS with pruning by the glide criterion of thm:rows on the prefix already fixed:
// row 3 gives N | p_j p_{j+1} and N^2 < p_j p_{j+1}; row 4 gives N^2 | C_3 and C_3 > 0.
// At a leaf the remaining three entries are derived and the full criterion applied.
//
// Rule 8: progress, ETA, atomic checkpoint, resume.
use std::fs;
use std::io::Write;
use std::time::Instant;

type I = i128;

fn cint(ps: &[I], n2: I) -> I {              // homogenised continuant C_k
    let (mut a, mut b) = (0 as I, 1 as I);   // C_{k-1}, C_k
    for &p in ps { let t = p * b - n2 * a; a = b; b = t; }
    b
}

/// full criterion of thm:rows on a complete p-vector
fn ok_full(p: &[I], n: usize, nn: I, nv: I) -> bool {
    if p.iter().any(|&t| t <= 0) { return false; }
    for r in 2..=(n / 2) {
        for j in 0..n {
            let w: Vec<I> = (0..r - 1).map(|i| p[(j + i) % n]).collect();
            let c = cint(&w, nn);
            if c <= 0 { return false; }
            let mut d: I = 1;
            for _ in 0..(r - 2) { d *= nv; }
            if c % d != 0 { return false; }
        }
    }
    true
}

/// prefix pruning: rows 3 and 4 on windows entirely inside the fixed prefix
fn ok_prefix(p: &[I], nn: I, nv: I) -> bool {
    let k = p.len();
    if k >= 2 {
        let (a, b) = (p[k - 2], p[k - 1]);
        if (a * b) % nv != 0 || a * b <= nn { return false; }
    }
    if k >= 3 {
        let (a, b, c) = (p[k - 3], p[k - 2], p[k - 1]);
        let c3 = c * (a * b - nn) - nn * a;
        if c3 <= 0 || c3 % nn != 0 { return false; }
    }
    true
}

fn count(n: usize, nv: I) -> u64 {
    let nn = nv * nv;
    let k = n - 3;
    let bound: I = (n as I - 4) * nv * nv * nv + 2 * nn;
    let nthreads: I = std::thread::available_parallelism().map(|x| x.get() as I).unwrap_or(4);
    let total = std::sync::Arc::new(std::sync::atomic::AtomicU64::new(0));
    let mut handles = Vec::new();
    for t in 0..nthreads {
        let total = std::sync::Arc::clone(&total);
        handles.push(std::thread::spawn(move || {
            let mut local: u64 = 0;
            let mut p: Vec<I> = Vec::with_capacity(k);
            let mut v0 = t + 1;
            while v0 <= bound {
                p.push(v0);
                rec(&mut p, k, n, nv, nn, bound, &mut local);
                p.pop();
                v0 += nthreads;
            }
            total.fetch_add(local, std::sync::atomic::Ordering::Relaxed);
        }));
    }
    for h in handles { h.join().unwrap(); }
    total.load(std::sync::atomic::Ordering::Relaxed)
}

fn rec(p: &mut Vec<I>, k: usize, n: usize, nv: I, nn: I, bound: I, total: &mut u64) {
    if p.len() == k {
        let np4 = { let mut d: I = 1; for _ in 0..(n - 4) { d *= nv; } d };
        let np5 = { let mut d: I = 1; for _ in 0..(n - 5) { d *= nv; } d };
        let e_num = cint(&p[..], nn);
        if e_num % np4 != 0 { return; }
        let e = e_num / np4;
        if e <= 0 { return; }
        let ah = cint(&p[..k - 1], nn) + np4;
        let bh = cint(&p[1..], nn) + np4;
        let den = e * np5;
        if den == 0 || (nv * ah) % den != 0 || (nv * bh) % den != 0 { return; }
        let mut full = p.clone();
        full.push((nv * ah) / den);
        full.push(e);
        full.push((nv * bh) / den);
        if ok_full(&full, n, nn, nv) { *total += 1; }
        return;
    }
    for v in 1..=bound {
        p.push(v);
        if ok_prefix(p, nn, nv) { rec(p, k, n, nv, nn, bound, total); }
        p.pop();
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args[1].parse().unwrap();
    let hi: I = args[2].parse().unwrap();
    let path = format!("../data/T{}.txt", n);
    let tmp = format!("{}.tmp", path);
    let mut rows: Vec<(I, u64)> = Vec::new();
    let mut start: I = 1;
    if let Ok(t) = fs::read_to_string(&path) {
        for l in t.lines().skip(1) {
            let q: Vec<&str> = l.split(',').collect();
            if q.len() == 2 {
                if let (Ok(a), Ok(b)) = (q[0].parse::<I>(), q[1].parse::<u64>()) {
                    rows.push((a, b)); start = a + 1;
                }
            }
        }
        eprintln!("resumed at N = {}", start);
    }
    let t0 = Instant::now();
    for nv in start..=hi {
        let c = count(n, nv);
        rows.push((nv, c));
        let el = t0.elapsed().as_secs_f64();
        let done = (nv - start + 1) as f64;
        let eta = el * ((hi - start + 1) as f64 - done) / done.max(1.0);
        eprintln!("n={} N={}  T = {}   box={}   {:.0}s elapsed, ETA {:.0}s",
                  n, nv, c, (n as I - 4) * nv * nv * nv + 2 * nv * nv, el, eta);
        let mut f = fs::File::create(&tmp).unwrap();
        writeln!(f, "N,\"T(N,{})\"", n).unwrap();
        for (a, b) in &rows { writeln!(f, "{},{}", a, b).unwrap(); }
        f.sync_all().unwrap();
        fs::rename(&tmp, &path).unwrap();
    }
}
