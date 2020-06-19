use clap::Clap;
use itertools::Itertools;
use num::integer::gcd;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::atomic::{AtomicBool, Ordering};

static MAKE_REPORT: AtomicBool = AtomicBool::new(false);

macro_rules! write_report(
    ($($args:tt)*) => {
        if MAKE_REPORT.load(Ordering::SeqCst) {
            print!($($args)*);
        }
    }
);

macro_rules! writeln_report(
    ($($args:tt)*) => {
        if MAKE_REPORT.load(Ordering::SeqCst) {
            println!($($args)*);
        }
    }
);

fn has_square_factor(d: i64) -> Result<(), i64> {
    let mut d = d.abs();
    assert_ne!(d, 0);

    let mut i = 2;
    while d != 1 {
        if d % i == 0 {
            d /= i;
            if d % i == 0 {
                return Err(i);
            }
        }

        i += 1;
    }

    Ok(())
}

fn discriminant(d: i64) -> i64 {
    let mod4 = (d % 4 + 4) % 4;
    writeln_report!(
        r"${} \equiv {} \mod 4$であるから，判別式を$D$とすると",
        d,
        mod4
    );
    // 負の時の対策
    let disc = if mod4 == 1 { d } else { 4 * d };
    writeln_report!(r"$D = {}$となる．", disc);

    disc
}

fn is_int(x: f64) -> bool {
    (x - x.round()).abs() < 1e-8
}

#[allow(clippy::cognitive_complexity, clippy::nonminimal_bool)]
fn calc_negative(disc: i64) -> Result<Vec<(i64, i64, i64)>, String> {
    writeln_report!("まず，条件を満たす$b$の候補を計算する．$b$の範囲は");
    // b の範囲を求める (exclusive)
    let maxb = {
        let sqrt = (disc.abs() as f64 / 3.0).sqrt();
        let is_int = is_int(sqrt);
        // 1.3 -> 2, 2.9 -> 3, 4.0 -> 5 としたい。
        //
        // sqrt.floor() + 1.0 でもよいが、 sqrt の精度で整数がわずかに小さい値に
        // なって floor で 1 ずれる可能性を心配している。
        let maxb = if is_int {
            sqrt.round() + 1.0
        } else {
            sqrt.ceil()
        } as i64;

        writeln_report!(
            r"\[ |b| \leqq  \sqrt{{ \frac{{ |{disc}| }}{{ 3 }} }} = \sqrt{{ \frac{{ |{discabs}| }}{{ 3 }} }} {op} {maxb}. \]",
            disc = disc,
            discabs = disc.abs(),
            op = if is_int { r"=" } else { "<" },
            maxb = if is_int { maxb - 1 } else { maxb },
        );

        maxb
    };

    writeln_report!(
        r"$4ac = b^2 + {}$より$b$は{}であるから，",
        disc.abs(),
        if disc % 2 == 0 { "偶数" } else { "奇数" }
    );
    let bs = (0..maxb)
        .filter(|x| x % 2 == disc.abs() % 2)
        .flat_map(|x| vec![x, -x])
        .dedup()
        .collect_vec();

    {
        let nonzero = bs.iter().filter(|&&x| x > 0);
        let has_zero = bs[0] == 0;
        if bs.is_empty() {
            writeln_report!(r"条件を満たす$b$はない．",);
            return Err("no cands; is d = 1?".to_string());
        }

        if bs.len() == 1 {
            writeln_report!(r"条件を満たす$b$は$b = 0$．",);
        } else {
            writeln_report!(
                r"条件を満たす$b$は$b = {}$\pm {}$．",
                if has_zero { "0$, " } else { "$" },
                nonzero.format(r"$, $\pm ")
            );
        }
    }

    writeln_report!();
    writeln_report!(r"その上で$a \leqq c, c > 0$となるような$a, c$を求める．");

    writeln_report!(r"\begin{{itemize}}");
    // 条件を満たす a, c を求める．
    let mut res = Vec::new();
    for b in bs {
        let do_report = b >= 0;

        if do_report {
            writeln_report!(
                r"\item $b = {}{}$のとき \\",
                if b != 0 { r"\pm " } else { "" },
                b
            );
        }

        let ac4 = b * b - disc;
        if ac4 % 4 != 0 {
            if do_report {
                writeln_report!(r"$4ac = {}$となり，これは整数解を持たない．", ac4);
            }
            continue;
        }

        let ac = ac4 / 4;
        if do_report {
            writeln_report!(r"$4ac = {}$より$ac = {}$．", ac4, ac);
            write_report!(r"よって$(a, c) = $");
        }
        let mut first = true;
        for a in -ac..=ac {
            if a == 0 || ac % a != 0 {
                continue;
            }
            let c = ac / a;
            if a <= c && c > 0 {
                if do_report {
                    write_report!("{}$({}, {})$", if first { "" } else { ", " }, a, c);
                    first = false;
                }
                res.push((a, b, c));
            }
        }
        if do_report {
            writeln_report!("．");
        }
    }
    writeln_report!(r"\end{{itemize}}");

    res.sort();
    res.dedup();
    res.sort_by_key(|&(a, b, c)| (a.abs(), b.abs(), c.abs()));
    writeln_report!(r"以上により，ここまでの条件を満たす$(a, b, c)$の組は");
    writeln_report!(r"$(a, b, c) = $ ${:?}$．", res.iter().format("$, $"));

    // 条件 (B) をチェックする
    fn cond(&(a, b, c): &(i64, i64, i64)) -> bool {
        writeln_report!(r"\item $(a, b, c) = ({}, {}, {})$のとき \\", a, b, c);
        let g = gcd(gcd(a, b), c);
        if g != 1 {
            writeln_report!("最大公約数が${}$となるので不適．", g);
            return false;
        }

        let left = -a < b && b <= a && a < c;
        let right = 0 <= b && b <= a && a == c;

        if left {
            writeln_report!(
                r"これは左側の不等式${} < {} \leqq {} < {}$を満たす．",
                -a,
                b,
                a,
                c
            );
            return true;
        }

        if right {
            writeln_report!(
                r"これは右側の不等式$0 \leqq {} \leqq {} = {}$満たす．",
                b,
                a,
                c
            );
            return true;
        }

        let left_failure = if !(-a < b) {
            format!(r"$-a < b$について${} \not< {}$", -a, b)
        } else if !(b <= a) {
            format!(r"$b \leqq a$について${} \not\leqq {}$", b, a)
        } else if !(a < c) {
            format!(r"$a < c$について${} \not< {}$", a, c)
        } else {
            unreachable!()
        };

        let right_failure = if !(0 <= b) {
            format!(r"$0 \leqq b$について${} \not\leqq {}$", 0, b)
        } else if !(b <= a) {
            format!(r"$b \leqq a$について${} \not\leqq {}$", b, a)
        } else if !(a == c) {
            format!(r"$a = c$について${} \neq {}$", a, c)
        } else {
            unreachable!()
        };

        writeln_report!("この組は左側の不等式では{}であり，右側の不等式では{}であるから，両方の不等式を満たさない.", left_failure, right_failure);
        false
    }
    writeln_report!(r"\begin{{itemize}}");
    res.retain(cond);
    writeln_report!(r"\end{{itemize}}");

    writeln_report!(
        "以上により，全ての条件を満たす$(a, b, c)$の組は${:?}$となる．",
        res.iter().format("$, $")
    );

    Ok(res)
}

#[allow(clippy::cognitive_complexity, clippy::nonminimal_bool)]
fn calc_positive(disc: i64) -> Result<Vec<(i64, i64, i64)>, String> {
    assert!(disc > 0);

    // 条件 (A) を確認する
    // b の候補を得る (exclusive))
    writeln_report!("まず，条件を満たす$b$の候補を計算する．$b$の範囲は");
    let minb = {
        let sqrt = (disc as f64).sqrt();
        // 本来は d = 1 以外で int になることはないのであまり考える必要はない。
        let is_int = is_int(sqrt);
        // 1.3 -> -2, -2.9 -> -3, 4.0 -> -4 としたい。
        let minb = if is_int { -sqrt.round() } else { -sqrt.ceil() } as i64;

        writeln_report!(
            r"\[ 0 > b > -\sqrt{{ {disc} }} {op} {minb}. \]",
            disc = disc,
            op = if is_int { "=" } else { ">" },
            minb = if is_int { minb - 1 } else { minb },
        );

        minb
    };

    writeln_report!(
        r"$4ac = b^2 - {}$より$b$は{}であるから，",
        disc,
        if disc % 2 == 0 { "偶数" } else { "奇数" }
    );
    let bs = ((minb + 1)..0).filter(|x| x.abs() % 2 == disc % 2);
    if bs.clone().collect_vec().is_empty() {
        writeln_report!(r"条件を満たす$b$はない．");
        return Err("no cands".to_string());
    }

    writeln_report!(r"条件を満たす$b$は$b = $ ${}$．", bs.clone().format("$, $"));

    // a, c を求める
    writeln_report!();
    writeln_report!("その上で$a > 0, c < 0$となる$a, c$を求める．");
    let mut res = Vec::new();

    writeln_report!(r"\begin{{itemize}}");
    for b in bs {
        writeln_report!(r"\item $b = {}$のとき \\", b);
        let ac4 = b * b - disc;
        if ac4 % 4 != 0 {
            writeln_report!("$4ac = {}$となり，これは整数解を持たない．", ac4);
            continue;
        }

        let ac = ac4 / 4;
        writeln_report!("$4ac = {}$より$ac = {}$．", ac4, ac);
        write_report!("よって$(a, c) = $");
        let mut first = true;
        for a in 0..=-ac {
            if a == 0 || ac % a != 0 {
                continue;
            }

            let c = ac / a;
            assert!(c < 0);
            write_report!("{}$({}, {})$", if first { "" } else { ", " }, a, c);
            first = false;
            res.push((a, b, c));
        }
        writeln_report!("．");
    }
    writeln_report!(r"\end{{itemize}}");

    writeln_report!(r"以上により，ここまでの条件を満たす$(a, b, c)$の組は");
    writeln_report!(r"$(a, b, c) = $ ${:?}$．", res.iter().format("$, $"));

    // 条件 (B) を確認する
    fn cond(&(a, b, c): &(i64, i64, i64)) -> bool {
        writeln_report!(r"\item $(a, b, c) = ({}, {}, {})$のとき \\", a, b, c);
        let g = gcd(gcd(a, b), c);
        if g != 1 {
            writeln_report!("最大公約数が${}$となるので不適．", g);
            return false;
        }

        let left = a + b + c < 0;
        let leftopnot = if !left { r"\not" } else { "" };
        let leftend = if left {
            "を満たす．"
        } else {
            "となるので不適．"
        };
        let right = a - b + c > 0;
        let rightopnot = if !right { r"\not" } else { "" };
        let rightstart = if left && right {
            "また"
        } else {
            "このとき"
        };
        let rightend = if right {
            "を満たす．"
        } else {
            "となるので不適．"
        };

        if !left || (left && right) {
            writeln_report!(
                r"このとき$a + b + c = {} {:+} {:+} = {} {}< 0${}",
                a,
                b,
                c,
                a + b + c,
                leftopnot,
                leftend
            );
        }
        if !right || (left && right) {
            writeln_report!(
                r"{}$a - b + c = {} {:+} {:+} = {} {}> 0${}",
                rightstart,
                a,
                -b,
                c,
                a - b + c,
                rightopnot,
                rightend
            );
        }

        left && right
    }
    writeln_report!(r"\begin{{itemize}}");
    res.retain(cond);
    writeln_report!(r"\end{{itemize}}");

    // 条件 (C) を確認する
    let res = remove_same_repeat(disc, &res);

    writeln_report!();
    writeln_report!(
        "以上により，全ての条件を満たす$(a, b, c)$の組は${:?}$となる．",
        res.iter().format("$, $")
    );

    Ok(res)
}

fn remove_same_repeat(disc: i64, cands: &[(i64, i64, i64)]) -> Vec<(i64, i64, i64)> {
    writeln_report!("");
    writeln_report!("ここまでで得られた$(a, b, c)$の組は，");
    writeln_report!(r"${:?}$．", cands.iter().format("$, $"));
    writeln_report!(r"これを連分数展開し，循環節が同じものを除く．");
    writeln_report!(r"連分数展開の途中に現れた分数を全て除けば良い．");
    let cand_fracs = cands
        .iter()
        .map(|&(a, b, _)| Frac::from_abd(a, b, disc))
        .collect_vec();
    let map: HashMap<_, _> = cand_fracs
        .iter()
        .copied()
        .zip(cands.iter().copied())
        .collect();
    let mut notfound: HashSet<_> = map.keys().collect();

    let mut res = Vec::new();
    for mut frac in cand_fracs {
        if !notfound.contains(&frac) {
            continue;
        }

        writeln_report!();
        writeln_report!("${:?}$に対応する${}$を連分数展開する．", map[&frac], frac);
        res.push(map[&frac]);
        notfound.remove(&frac);

        let mut obtained = HashSet::new();
        while obtained.insert(frac) && !notfound.is_empty() {
            write_report!(r"\[ {} = ", frac);
            let int = frac.integer_part();
            frac = frac.sub_int(int);
            write_report!(r"{} + \left({}\right) = ", int, frac);
            frac = frac.invert();
            writeln_report!(r"{} + \frac{{ 1 }}{{ {} }}. \]", int, frac);
            if notfound.contains(&frac) {
                writeln_report!(
                    "${}$は${:?}$に対応するので，${:?}$は除く．",
                    frac,
                    map[&frac],
                    map[&frac]
                );
                notfound.remove(&frac);
            }
        }

        if !notfound.is_empty() && obtained.contains(&frac) {
            writeln_report!(
                "ここで${}$は一度現れたので，この連分数はここから循環する．",
                frac
            );
        }
    }

    res
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
struct Frac {
    num: i64,
    coeff: i64,
    root: i64,
    denom: i64,
}

impl fmt::Display for Frac {
    fn fmt(&self, b: &mut fmt::Formatter) -> fmt::Result {
        let coeff = if self.coeff == 1 {
            "+".to_string()
        } else if self.coeff == -1 {
            "-".to_string()
        } else {
            format!("{:+}", self.coeff)
        };
        let num = format!(r"{} {}\sqrt{{ {} }}", self.num, coeff, self.root);
        let frac = if self.denom == 1 {
            num
        } else {
            format!(r"\frac{{ {} }}{{ {} }}", num, self.denom)
        };

        write!(b, "{}", frac)
    }
}

impl Frac {
    pub fn from_abd(a: i64, b: i64, disc: i64) -> Frac {
        Frac::new(-b, 1, disc, 2 * a)
    }

    pub fn new(num: i64, coeff: i64, root: i64, denom: i64) -> Frac {
        assert!(root > 0);
        let mut f = Frac {
            num,
            coeff,
            root,
            denom,
        };
        f.normalize();
        f
    }

    pub fn normalize(&mut self) {
        self.normalize_root();
        self.reduce();
        if self.denom < 0 {
            self.denom *= -1;
            self.num *= -1;
            self.coeff *= -1;
        }
    }

    pub fn invert(self) -> Frac {
        let denom = self.num * self.num - self.coeff * self.coeff * self.root;
        let num = self.denom * self.num;
        let coeff = -self.denom * self.coeff;
        let root = self.root;

        let mut res = Frac {
            denom,
            num,
            coeff,
            root,
        };
        res.normalize();

        res
    }

    pub fn integer_part(self) -> i64 {
        let num = self.num as f64 + self.coeff as f64 * (self.root as f64).sqrt();
        let denom = self.denom as f64;

        let float = num / denom;
        if is_int(float) {
            float.round() as i64
        } else {
            float.floor() as i64
        }
    }

    pub fn sub_int(mut self, int: i64) -> Frac {
        self.num -= int * self.denom;
        self.normalize();
        self
    }

    fn normalize_root(&mut self) {
        while let Err(d) = has_square_factor(self.root) {
            self.root /= d * d;
            self.coeff *= d;
        }
    }

    fn reduce(&mut self) {
        let g = gcd(gcd(self.num, self.coeff), self.denom);
        self.num /= g;
        self.coeff /= g;
        self.denom /= g;
    }
}

#[allow(clippy::collapsible_if)]
fn do_main(d: i64) -> Result<(), String> {
    // if d.abs() > 999 {
    //     return Err(format!("input too large: {}", d));
    // }

    if d == 0 {
        writeln_report!("$d = 0$ のときは考えない．");
        return Err("d is zero".to_string());
    }

    if let Err(f) = has_square_factor(d) {
        writeln_report!("$d = {}$は平方因子${}$を持つため，考えない．", d, f);
        return Err(format!("{} has square factor: {}", d, f));
    }

    writeln_report!(r"このとき$d = {}$である．", d);
    let disc = discriminant(d);
    writeln_report!();
    let res = if d < 0 {
        calc_negative(disc)?
    } else {
        calc_positive(disc)?
    };

    if !MAKE_REPORT.load(Ordering::SeqCst) {
        println!("d = {}: {} ({:?})", d, res.len(), res);
    }

    if MAKE_REPORT.load(Ordering::SeqCst) {
        writeln_report!("したがって，$h_K = {}$．", res.len());
        writeln_report!();
        writeln_report!("イデアル類群の代表元は，");
        let mut first = true;
        for (a, b, _) in res {
            if !first {
                write_report!(", ");
            }
            first = false;

            if b % 2 == 0 && disc % 4 == 0 {
                if b == 0 {
                    write_report!(r"$\left({}, \sqrt{{ {} }}\right)$", a, disc / 4);
                } else {
                    write_report!(
                        r"$\left({}, {} + \sqrt{{ {} }}\right)$",
                        a,
                        -b / 2,
                        disc / 4
                    );
                }
            } else {
                if b == 0 {
                    write_report!(
                        r"$\left({}, \frac{{ \sqrt{{ {} }} }}{{ 2 }}\right)$",
                        a,
                        disc
                    );
                } else {
                    write_report!(
                        r"$\left({}, \frac{{ {} + \sqrt{{ {} }} }}{{ 2 }}\right)$",
                        a,
                        -b,
                        disc
                    );
                }
            }
        }
        writeln_report!(r"．");
    }

    Ok(())
}

#[derive(Clap)]
struct Opt {
    #[clap(short = "r", long, about = "Enables reporting")]
    make_report: bool,
    start: i64,
    end: Option<i64>,
}

fn main() {
    let opt = Opt::parse();

    if opt.make_report {
        MAKE_REPORT.store(true, Ordering::SeqCst);
    }

    let start = opt.start;
    let end = opt.end.unwrap_or(opt.start);
    for d in start..=end {
        writeln_report!();
        writeln_report!(r"\section{{ $K = \mathbb{{Q}}(\sqrt{{ {} }})$ }}", d);
        writeln_report!();

        let _ = do_main(d);
    }
}
