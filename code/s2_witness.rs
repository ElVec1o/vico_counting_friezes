// For contributing t <= T, record the MINIMAL witness k (w = kt-1 divides p+t).
// If almost all contributors have small k, S2 follows from a Shiu-type bound:
//   #{t : minimal k <= K} <= sum_{k<=K} d(kp+1) << K log p.
fn is_prime(n: u64) -> bool { if n<2 {return false;} let mut d=2u64; while d*d<=n { if n%d==0 {return false;} d+=1; } true }
fn min_k(p: u64, t: u64) -> Option<u64> {
    let m = p + t;
    if t == 1 { return Some(1); }
    let mut best: Option<u64> = None;
    let mut i = 1u64;
    while i*i <= m {
        if m % i == 0 {
            for w in [i, m/i] {
                if (w + 1) % t == 0 {
                    let k = (w + 1) / t;
                    best = Some(match best { None => k, Some(b) => if k < b { k } else { b } });
                }
            }
        }
        i += 1;
    }
    best
}
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let start: u64 = args[1].parse().unwrap();
    let count: usize = args[2].parse().unwrap();
    println!("          p       T   contrib   k<=1  k<=4  k<=16  k<=64  k<=T   maxk");
    let mut found = 0; let mut c = start;
    while found < count {
        if is_prime(c) {
            let tmax = ((2.0*c as f64).powf(1.0/3.0)) as u64;
            let (mut n, mut a, mut b, mut d, mut e, mut f, mut mx) = (0u64,0u64,0u64,0u64,0u64,0u64,0u64);
            for t in 1..=tmax {
                if let Some(k) = min_k(c, t) {
                    n += 1;
                    if k <= 1 { a += 1; } if k <= 4 { b += 1; } if k <= 16 { d += 1; }
                    if k <= 64 { e += 1; } if k <= tmax { f += 1; }
                    if k > mx { mx = k; }
                }
            }
            println!(" {:>10} {:>7} {:>9} {:>6} {:>5} {:>6} {:>6} {:>6} {:>6}",
                     c, tmax, n, a, b, d, e, f, mx);
            found += 1; c += start/5 + 1;
        } else { c += 1; }
    }
}
