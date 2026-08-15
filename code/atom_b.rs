// ATOM B: #{t >= 1 : p+t has a divisor = -1 mod t}.
// The whole 1/3 -> eps gap is whether this is p^{o(1)}.
// Rule 8: progress, ETA, atomic checkpoint, resume.
use std::fs; use std::io::Write; use std::time::Instant;
fn spf_sieve(n: usize) -> Vec<u32> {
    let mut s: Vec<u32> = (0..=n).map(|i| i as u32).collect();
    let mut i = 2usize;
    while i*i <= n { if s[i]==i as u32 { let mut j=i*i; while j<=n { if s[j]==j as u32 {s[j]=i as u32;} j+=i; } } i+=1; }
    s
}
fn divisors(mut n: usize, spf: &[u32]) -> Vec<u64> {
    let mut ds: Vec<u64> = vec![1];
    while n > 1 { let p = spf[n] as usize; let mut k=0;
        while n % p == 0 { n/=p; k+=1; }
        let len = ds.len(); let mut pw: u64 = 1;
        for _ in 0..k { pw *= p as u64; for i in 0..len { let d = ds[i]*pw; ds.push(d); } } }
    ds
}
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let hi: usize = args[1].parse().unwrap();
    // Output file: second argument, or atomB.csv in the working directory.
    let path: String = args.get(2).cloned().unwrap_or_else(|| "atomB.csv".to_string());
    let spf = spf_sieve(2*hi + 10);
    let t0 = Instant::now();
    let mut rows: Vec<(usize,usize,usize,usize)> = Vec::new();
    let mut n = 5usize;
    while n <= hi {
        // primality
        let mut isp = n > 1; let mut d = 2;
        while d*d <= n { if n%d==0 { isp=false; break; } d+=1; }
        if isp {
            let mut contrib = 0usize; let mut total = 0usize; let mut mx = 0usize;
            for t in 1..=(n+2) {
                let m = n + t;
                if m > 2*hi { break; }
                let mut c = 0usize;
                for &w in divisors(m, &spf).iter() { if (w as usize + 1) % t == 0 { c += 1; } }
                if c > 0 { contrib += 1; total += c; if c > mx { mx = c; } }
            }
            rows.push((n, contrib, total, mx));
            if rows.len() % 20 == 0 {
                let el = t0.elapsed().as_secs_f64();
                eprintln!("p={} contrib={} C={} max={}  {:.0}s elapsed", n, contrib, total, mx, el);
                let mut f = fs::File::create(format!("{}.tmp", path)).unwrap();
                writeln!(f, "p,contrib,C,maxterm").unwrap();
                for r in &rows { writeln!(f, "{},{},{},{}", r.0,r.1,r.2,r.3).unwrap(); }
                f.sync_all().unwrap(); fs::rename(format!("{}.tmp",path), &path).unwrap();
            }
        }
        n += 1;
    }
    let mut f = fs::File::create(format!("{}.tmp", path)).unwrap();
    writeln!(f, "p,contrib,C,maxterm").unwrap();
    for r in &rows { writeln!(f, "{},{},{},{}", r.0,r.1,r.2,r.3).unwrap(); }
    f.sync_all().unwrap(); fs::rename(format!("{}.tmp",path), &path).unwrap();
    eprintln!("done, {} primes", rows.len());
}
