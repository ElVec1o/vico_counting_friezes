// The function-field analogue of Conrey's conjecture, in the toy universe F_q[t].
//
// Over Z the width-5 count at a prime is C(p) = #{(a,u,v) in Z_{>0}^3 : a u v = p + u + v},
// and conj:order asserts C(p) = p^{o(1)}. The analogue over F_q[t] is
//
//     C(P) = #{(A,U,V) in (F_q[t] \ {0})^3 : A U V = P + U + V},   P irreducible, deg P = n,
//
// and the analogue of conj:order is C(P) = q^{o(n)}, i.e. subexponential in n.
//
// Solving for V gives V (A U - 1) = P + U, so V is determined by (A,U) whenever
// (A U - 1) | (P + U). Degrees: A U V = P + U + V forces deg A + deg U + deg V <= n,
// so the enumeration over deg A + deg U <= n is complete, not a truncation.
//
// PRE-REGISTERED PREDICTION (frozen before this program was run):
//   under log p <-> n, the heuristic C(p) ~ log^2 p predicts C(P) QUADRATIC in n,
//   hence q^{o(n)}, plus a q-dependent additive term from deg A = deg U = 0.
//
// Usage:  ff_conrey <q> <nmax> <samples>

use std::env;
use std::time::Instant;

type P = Vec<u32>; // little endian coefficients mod q; no trailing zeros; empty = 0

fn norm(mut a: P, _q: u32) -> P { while a.last() == Some(&0) { a.pop(); } a }
fn deg(a: &P) -> i32 { a.len() as i32 - 1 }

fn add(a: &P, b: &P, q: u32) -> P {
    let n = a.len().max(b.len());
    let mut r = vec![0u32; n];
    for i in 0..n {
        let x = if i < a.len() { a[i] } else { 0 };
        let y = if i < b.len() { b[i] } else { 0 };
        r[i] = (x + y) % q;
    }
    norm(r, q)
}

fn mul(a: &P, b: &P, q: u32) -> P {
    if a.is_empty() || b.is_empty() { return vec![]; }
    let mut r = vec![0u32; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        if x == 0 { continue; }
        for (j, &y) in b.iter().enumerate() {
            r[i + j] = (r[i + j] + x * y) % q;
        }
    }
    norm(r, q)
}

fn inv(x: u32, q: u32) -> u32 { (1..q).find(|&y| x * y % q == 1).unwrap() }

// returns (quotient, remainder)
fn divmod(a: &P, b: &P, q: u32) -> (P, P) {
    if deg(a) < deg(b) { return (vec![], a.clone()); }
    let mut r = a.clone();
    let db = deg(b) as usize;
    let lb = inv(b[db], q);
    let mut quo = vec![0u32; (deg(a) - deg(b) + 1) as usize];
    while !r.is_empty() && deg(&r) >= deg(b) {
        let dr = deg(&r) as usize;
        let c = r[dr] * lb % q;
        let sh = dr - db;
        quo[sh] = c;
        for i in 0..=db {
            r[i + sh] = (r[i + sh] + q - c * b[i] % q) % q;
        }
        r = norm(r, q);
    }
    (norm(quo, q), r)
}

fn from_index(mut k: u64, d: u32, q: u32) -> P { // all polys of degree exactly d
    let mut c = vec![0u32; (d + 1) as usize];
    for i in 0..d { c[i as usize] = (k % q as u64) as u32; k /= q as u64; }
    c[d as usize] = 1 + (k % (q as u64 - 1)) as u32; // nonzero leading
    c
}

fn count_degree(d: u32, q: u32) -> u64 { (q as u64).pow(d) * (q as u64 - 1) }

fn is_irred(p: &P, q: u32) -> bool {
    let n = deg(p);
    if n < 1 { return false; }
    for d in 1..=(n / 2) {
        for k in 0..count_degree(d as u32, q) {
            let f = from_index(k, d as u32, q);
            if divmod(p, &f, q).1.is_empty() { return false; }
        }
    }
    true
}

fn count(p: &P, q: u32) -> u64 {
    let n = deg(p);
    let one: P = vec![1];
    let mut total = 0u64;
    for da in 0..=n {
        for ka in 0..count_degree(da as u32, q) {
            let a = from_index(ka, da as u32, q);
            for du in 0..=(n - da) {
                for ku in 0..count_degree(du as u32, q) {
                    let u = from_index(ku, du as u32, q);
                    let m = add(&mul(&a, &u, q), &vec![q - 1], q); // A U - 1
                    if m.is_empty() { continue; }
                    let r = add(p, &u, q); // P + U
                    let (v, rem) = divmod(&r, &m, q);
                    if rem.is_empty() && !v.is_empty() { total += 1; }
                }
            }
        }
    }
    total
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let q: u32 = args.get(1).map(|s| s.parse().unwrap()).unwrap_or(2);
    let nmax: i32 = args.get(2).map(|s| s.parse().unwrap()).unwrap_or(12);
    let samples: usize = args.get(3).map(|s| s.parse().unwrap()).unwrap_or(3);
    let t0 = Instant::now();
    println!("  q = {}   C(P) = #{{(A,U,V) nonzero : A U V = P + U + V}},  P irreducible", q);
    println!("    n     irreducibles used     min C      max C      mean C     mean/n^2");
    for n in 2..=nmax {
        let mut cs = vec![];
        let tot = count_degree(n as u32, q);
        let mut k = 0u64;
        while k < tot && cs.len() < samples {
            let f = from_index(k, n as u32, q);
            if is_irred(&f, q) { cs.push(count(&f, q)); }
            k += 1;
        }
        if cs.is_empty() { continue; }
        let mn = *cs.iter().min().unwrap();
        let mx = *cs.iter().max().unwrap();
        let mean = cs.iter().sum::<u64>() as f64 / cs.len() as f64;
        println!("  {:>3}   {:>10}          {:>8}   {:>8}   {:>9.1}    {:>8.3}",
                 n, cs.len(), mn, mx, mean, mean / (n * n) as f64);
    }
    eprintln!("  elapsed {:.1}s", t0.elapsed().as_secs_f64());
}
