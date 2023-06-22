//! This module provides an implementation of polynomials over bls12_381::Scalar

// use bls12_381::Scalar;
use itertools::Either;

use crate::Scalar;

use std::{
    borrow::{Cow, Borrow},
    fmt, mem::{self, replace},
    ops::{AddAssign, Div, Mul, MulAssign, SubAssign, Index, IndexMut}, collections::VecDeque, iter::empty,
};

/// A polynomial with bl12_381::Scalar factors
#[derive(Clone, Debug, Eq)]
pub enum Poly<'a> {
    Borrowed(&'a [Scalar]),
    Owned([Scalar; 1]),
    Allocated(VecDeque<Scalar>),
}

impl<'a> From<&'a [Scalar]> for Poly<'a> {
    fn from(v: &'a [Scalar]) -> Self {
        Poly::Borrowed(v).normalize_self()
    }
}

impl<'a> From<[Scalar; 1]> for Poly<'a> {
    fn from(v: [Scalar; 1]) -> Self {
        Poly::Owned(v).normalize_self()
    }
}

impl<'a, const S: usize> From<&'a [Scalar; S]> for Poly<'a> {
    fn from(v: &'a [Scalar; S]) -> Self {
        v.as_slice().into()
    }
}

impl<'a> From<[u64; 1]> for Poly<'a> {
    fn from(v: [u64; 1]) -> Self {
        Poly::Owned(v.map(Scalar::from)).normalize_self()
    }
}
impl<'a> From<Vec<Scalar>> for Poly<'a> {
    fn from(v: Vec<Scalar>) -> Self {
        Poly::Allocated(v.into()).normalize_self()
    }
}
impl<'a> From<VecDeque<Scalar>> for Poly<'a> {
    fn from(v: VecDeque<Scalar>) -> Self {
        Poly::Allocated(v).normalize_self()
    }
}
impl<'a, 'b> PartialEq<Poly<'b>> for Poly<'a> {
    fn eq(&self, other: &Poly<'b>) -> bool {
        match (self, other) {
            (Self::Borrowed(s), Poly::Borrowed(o)) => s == o,
            (Self::Borrowed(s), Poly::Owned(o)) => s == o,
            (Self::Borrowed(s), Poly::Allocated(o)) => o == s,
            (Self::Owned(s), Poly::Borrowed(o)) => s == o,
            (Self::Owned(s), Poly::Owned(o)) => s == o,
            (Self::Owned(s), Poly::Allocated(o)) => o == s,
            (Self::Allocated(s), Poly::Borrowed(o)) => s == o,
            (Self::Allocated(s), Poly::Owned(o)) => s == o,
            (Self::Allocated(s), Poly::Allocated(o)) => s == o,
        }
    }
}

impl<'a> Poly<'a> {
    /// Creates a new Poly from its `coeffs`icients, first element the coefficient for x^0
    /// for safetly, input value is normalized (trailing zeroes are removed)
    pub fn new(coeffs: impl Into<Self>) -> Self {
        coeffs.into()
    }

    /// Creates a new polynomial where the `coeffs` fits in u64 values
    pub fn from(coeffs: &[u64]) -> Self {
        Poly::new(
            coeffs
                .iter()
                .map(|n| Scalar::from(*n))
                .collect::<VecDeque<Scalar>>(),
        )
    }

    /// Returns p(x)=0
    pub fn zero() -> Self {
        Poly::Owned([Scalar::zero()])
    }

    /// Returns p(x)=1
    pub fn one() -> Self {
        Poly::Owned([Scalar::one()])
    }

    fn len(&self) -> usize {
        match self {
            Self::Borrowed(v) => v.len(),
            Self::Owned(v) => v.len(),
            Self::Allocated(v) => v.len(),
        }
    }

    fn into_vec_deque(self) -> VecDeque<Scalar> {
        match self {
            Self::Borrowed(borrowed) => {
                let mut new = VecDeque::with_capacity(borrowed.len());
                new.extend(borrowed);
                new
            }
            Self::Owned(owned) => owned.into(),
            Self::Allocated(allocated) => allocated,
        }
    }

    fn to_vec_deque(&mut self) -> &mut VecDeque<Scalar> {
        match *self {
            Self::Borrowed(borrowed) => {
                let mut new = VecDeque::with_capacity(borrowed.len());
                new.extend(borrowed);
                *self = Self::Allocated(new);
                match *self {
                    Self::Allocated(ref mut allocated) => allocated,
                    _ => unreachable!(),
                }
            }
            Self::Owned(owned) => {
                *self = Self::Allocated(owned.into());
                match *self {
                    Self::Allocated(ref mut allocated) => allocated,
                    _ => unreachable!(),
                }
            }
            Self::Allocated(ref mut allocated) => allocated,
        }
    }

    fn push_back(&mut self, v: Scalar) {
        match *self {
            Self::Borrowed(borrowed) => {
                let mut new = VecDeque::with_capacity(borrowed.len() + 1);
                new.extend(borrowed);
                new.push_back(v);
                *self = Self::Allocated(new);
            }
            Self::Owned(owned) => {
                let mut new = VecDeque::with_capacity(owned.len() + 1);
                new.extend(owned);
                new.push_back(v);
                *self = Self::Allocated(new);
            }
            Self::Allocated(ref mut allocated) => allocated.push_back(v),
        }
    }

    pub fn iter(&self) -> impl ExactSizeIterator+DoubleEndedIterator<Item = &Scalar> {
        match self {
            Self::Borrowed(b) => Either::Left(b.iter()),
            Self::Owned(o) => Either::Left(o.iter()),
            Self::Allocated(a) => Either::Right(a.iter()),
        }
    }
    pub fn iter_mut(&mut self) -> impl ExactSizeIterator+DoubleEndedIterator<Item = &mut Scalar> {
        match self {
            Self::Borrowed(borrowed) => {
                let mut new = VecDeque::with_capacity(borrowed.len());
                new.extend(*borrowed);
                *self = Self::Allocated(new);
                match *self {
                    Self::Allocated(ref mut allocated) => Either::Right(allocated.iter_mut()),
                    _ => unreachable!(),
                }
            }
            Self::Owned(o) => Either::Left(o.iter_mut()),
            Self::Allocated(a) => Either::Right(a.iter_mut()),
        }
    }

    pub fn z_poly_of<'b, I: IntoIterator<Item=&'b (Scalar, Scalar)>>(points: I) -> Self
    where I::IntoIter: ExactSizeIterator {
        let points = points.into_iter().map(|(z, _y)| z);
        Self::zero_poly(points).map(Poly::Allocated).unwrap_or_else(Poly::one)
    }

    fn zero_poly<'b, I: IntoIterator<Item=&'b Scalar>>(points: I) -> Option<VecDeque<Scalar>>
    where I::IntoIter: ExactSizeIterator {
        let mut points = points.into_iter();
        match points.next() {
            None => None,
            Some(z) => {
                let mut poly = VecDeque::with_capacity(points.len() + 1);
                poly.push_back(-z);
                poly.push_back(Scalar::one());
                Some(points.fold(poly, |mut poly, z| {
                    Poly::mul_by_x_sub_s(&mut poly, z);
                    poly
                }))
            }
        }
    }

    pub fn div_by_z_poly_of<'b, I: IntoIterator<Item=&'b (Scalar, Scalar)>>(self, points: I) -> Self {
        let mut q = self.into_vec_deque();
        for z in points.into_iter().map(|(z, _y)| z) {
            q = Poly::div_by_x_plus_s(q, &-z);
        }
        Poly::Allocated(q).normalize_self()
    }

    /// An optimized version of self / [s, 1]
    fn div_by_x_plus_s(mut p: VecDeque<Scalar>, s: &Scalar) -> VecDeque<Scalar> {
        let first = match p.get(0) {
            None => return p,
            Some(v) if v.is_zero_vartime() => return p,
            Some(v) => v,
        };
        let second = match p.get(1) {
            None => panic!("indivisible polynomial"),
            Some(v) => v,
        };

        let s_inv = s.invert().unwrap();
        let s_inv_sq = s_inv.square();

        let second = second * s - first;

        p[0] = first * s_inv;
        p[1] = second * s_inv_sq;
        p.pop_back();

        // if p[1].is_zero_vartime() && p.len() == 2 {
        //     p.pop_back();
        //     return p;
        // }

        let (mut prev, mut num, mut denom) = (second, *s, s_inv_sq);
        for v in p.iter_mut().skip(2) {
            num *= s;
            denom *= s_inv;
            prev = *v*num - prev;
            *v = prev * denom
        }
        p
    }
    
    fn div_by_x_plus_s_helper<'p>(p: &'p VecDeque<Scalar>, s: &'p Scalar, s_inv: &'p Scalar) -> impl Iterator<Item=Scalar> + 'p {
        let first = match p.get(0) {
            None => return Either::Left(empty()),
            Some(v) if v.is_zero_vartime() => return Either::Left(empty()),
            Some(v) => v,
        };
        let second = match p.get(1) {
            None => panic!("indivisible polynomial"),
            Some(v) => v,
        };
        let mut p = p.iter();
        p.nth(1);
        p.next_back();

        // let s_inv = s.invert().unwrap();
        let s_inv_sq = s_inv.square();

        let second = second * s - first;
        let (mut prev, mut num, mut denom) = (second, *s, s_inv_sq);

        let p = p.map(move |v| {
            num *= s;
            denom *= s_inv;
            prev = v*num - prev;
            prev * denom
        });
        let second = second * s_inv_sq;
        let second = if second.is_zero_vartime() && p.len() == 0 {
            None
        } else {
            Some(second)
        };
        Either::Right([first * s_inv].into_iter().chain(second).chain(p))
    }

    /// An optimized version of p *= [-s, 1]
    fn mul_by_x_sub_s(p: &mut VecDeque<Scalar>, s: &Scalar) {
        if p.is_empty() || (p.len() == 1 && p[0].is_zero_vartime()) {
            return
        }
        p.push_front(Scalar::zero());
        
        let mut p = p.iter_mut();
        let init = p.next().unwrap();
        p.fold(init, |prev, curr| {
            *prev -= *curr * s;
            curr
        });
    }

    pub fn evaluate_z_poly(points: impl IntoIterator<Item=&'a (Scalar, Scalar)>, x: &Scalar) -> Scalar {
        let mut points = points.into_iter();
        match points.next() {
            None => Scalar::one(),
            Some((z, _y)) => points.fold(x - z, |acc, (z, _y)| acc * (x - z)),
        }
    }

    /// Creates a polynomial that contains a set of `p` points, by using lagrange
    /// see https://en.wikipedia.org/wiki/Lagrange_polynomial
    /// # Examples
    /// ```
    ///    use a0kzg::{Poly, Scalar};
    ///    // f(x)=x is a polynomial that fits in (1,1), (2,2) points
    ///    assert_eq!(
    ///      Poly::lagrange(&[
    ///          (Scalar::from(1), Scalar::from(1)),
    ///          (Scalar::from(2), Scalar::from(2))
    ///      ]),
    ///      Poly::from(&[0, 1]) // f(x) = x
    ///    );
    /// ```
    pub fn lagrange2(p: &[(Scalar, Scalar)]) -> Self {
        let k = p.len();
        let mut l = Poly::zero();
        for j in 0..k {
            let mut denom = Scalar::one();
            let mut l_j = VecDeque::with_capacity(k);
            l_j.push_back(Scalar::one());
            for i in 0..k {
                if i == j { continue; }
                denom *= p[j].0 - p[i].0;
                Poly::mul_by_x_sub_s(&mut l_j, &p[i].0);
            }
            let mut l_j = Poly::Allocated(l_j);
            l_j *= &(p[j].1 * denom.invert().unwrap());
            l += &l_j;
        }
        assert_eq!(l.len(), p.len());
        l
    }
    /// Creates a polynomial that contains a set of `p` points, by using lagrange
    /// see https://en.wikipedia.org/wiki/Lagrange_polynomial
    /// # Examples
    /// ```
    ///    use a0kzg::{Poly, Scalar};
    ///    // f(x)=x is a polynomial that fits in (1,1), (2,2) points
    ///    assert_eq!(
    ///      Poly::lagrange(&[
    ///          (Scalar::from(1), Scalar::from(1)),
    ///          (Scalar::from(2), Scalar::from(2))
    ///      ]),
    ///      Poly::from(&[0, 1]) // f(x) = x
    ///    );
    /// ```
    pub fn lagrange(p: &[(Scalar, Scalar)]) -> Self {
        Self::lagrange_z_poly(p).0
    }

    /// Creates a polynomial that contains a set of `p` points, by using lagrange
    /// see https://en.wikipedia.org/wiki/Lagrange_polynomial
    /// # Examples
    /// ```
    ///    use a0kzg::{Poly, Scalar};
    ///    // f(x)=x is a polynomial that fits in (1,1), (2,2) points
    ///    assert_eq!(
    ///      Poly::lagrange(&[
    ///          (Scalar::from(1), Scalar::from(1)),
    ///          (Scalar::from(2), Scalar::from(2))
    ///      ]),
    ///      Poly::from(&[0, 1]) // f(x) = x
    ///    );
    /// ```
    pub fn lagrange_z_poly(p: &[(Scalar, Scalar)]) -> (Self, Self) {
        let k = p.len();
        let mut l = VecDeque::with_capacity(k);
        let zero_poly = match k {
            0 | 1 => None,
            _ => Self::zero_poly(p.iter().map(|(z, _)| z)),
        };

        let mut p_x_invert = vec![Scalar::zero(); k];
        Scalar::invert_batch(p.iter().map(|(x, _y)| -x), &mut p_x_invert);

        let mut p_y_denom = vec![Scalar::zero(); k];
        let mut p_y_denom_invert = vec![Scalar::zero(); k];
        for j in 0..k {
            let denom = p.iter().map(|(x, _y)| x);
            let mut denom = denom.clone().take(j).chain(denom.skip(j+1));
            match denom.next() {
                None => p_y_denom_invert[j] = Scalar::one(),
                Some(i) => {
                    p_y_denom[j] = denom.fold(p[j].0 - i, |denom, i| denom * (p[j].0 - i));
                },
            };
        }
        Scalar::invert_batch(p_y_denom.iter(), &mut p_y_denom_invert);

        for j in 0..k {
            let val = p[j].1 * p_y_denom_invert[j];
            match &zero_poly {
                Some(zero_poly) => mac_helper(&mut l, Self::div_by_x_plus_s_helper(zero_poly, &-p[j].0, &p_x_invert[j]), &val),
                None => add_helper(&mut l, [Cow::Owned(val)].into_iter()),
            };
        }
        
        assert_eq!(l.len(), k);
        (Poly::Allocated(l).normalize_self(), zero_poly.map(Poly::Allocated).unwrap_or_else(Poly::one))
    }

    pub fn evaluate_lagrange(p: &[(Scalar, Scalar)], x: &Scalar) -> Scalar {
        p.iter()
            .enumerate()
            .fold(Scalar::zero(), |sum, (i, (x_i, y_i))| {
                let mut p_j = p[0..i]
                    .iter()
                    .chain(p[i + 1..].iter())
                    .map(|(x_j, _y_j)| x_j);
                match p_j.next() {
                    None => sum + y_i,
                    Some(x_j) => {
                        let (num, denom) = p_j.fold((x - x_j, x_i - x_j), |(num, denom), x_j| {
                            (num * (x - x_j), denom * (x_i - x_j))
                        });
                        sum + y_i * num * denom.invert().unwrap()
                    }
                }
            })
    }

    /// Evals the polynomial at the desired point
    /// # Examples
    /// ```
    ///    use a0kzg::{Poly, Scalar};
    ///    // check that (x^2+2x+1)(2) = 9
    ///    assert_eq!(
    ///      Poly::from(&[1, 2, 1]).eval(&Scalar::from(2)),
    ///      Scalar::from(9));
    /// ```
    pub fn eval(&self, x: &Scalar) -> Scalar {
        let mut x_pow = Scalar::one();
        let mut y = self[0];
        for v in self.iter().skip(1) {
            x_pow *= x;
            y += &(x_pow * v);
        }
        y
    }

    /// Evals the polynomial suplying the `x_pows` x^0, x^1, x^2
    pub fn eval_with_pows(&self, x_pow: &[Scalar]) -> Scalar {
        self.iter()
            .zip(x_pow.iter())
            .fold(Scalar::one(), |mut y, (v, x)| {
                y += &(v * x);
                y
            })
    }

    /// Returns the degree of the polinominal, degree(x+1) = 1
    pub fn degree(&self) -> usize {
        self.len().saturating_sub(1)
    }

    /// Normalizes the coefficients, removing ending zeroes
    /// # Examples
    /// ```
    ///    use a0kzg::Poly;
    ///    let mut p1 = Poly::from(&[1, 0, 0, 0]);
    ///    p1.normalize();
    ///    assert_eq!(p1, Poly::from(&[1]));
    /// ```
    pub fn normalize(&mut self) {
        if self.iter().next_back().map(|v| v.is_zero_vartime()) == Some(true) {
            let zero = Scalar::zero();
            let first_non_zero = self.iter().rev().position(|p| p != &zero);
            if let Some(first_non_zero) = first_non_zero {
                let new_len = self.len() - first_non_zero;
                match self {
                    Self::Borrowed(v) => *self = Self::Borrowed(&v[..new_len]),
                    Self::Owned(v) => *self = Self::Allocated({
                        let mut new = VecDeque::with_capacity(new_len);
                        new.extend(&v[..new_len]);
                        new
                    }),
                    Self::Allocated(v) => v.truncate(new_len),
                }
            } else {
                match self {
                    Self::Borrowed(v) => *self = Self::Borrowed(&v[..1]),
                    Self::Owned(_) => *self = Self::zero(),
                    Self::Allocated(v) => v.truncate(1),
                }
            }
        }
    }

    pub fn normalize_self(mut self) -> Self {
        self.normalize();
        self
    }

    /// Returns if p(x)=0
    /// # Examples
    /// ```
    ///    use a0kzg::Poly;
    ///    assert!(Poly::zero().is_zero());
    ///    assert!(!Poly::one().is_zero());
    /// ```
    pub fn is_zero(&self) -> bool {
        self == &Poly::new(&[Scalar::zero()])
    }

    /// Sets the `i`-th coefficient to the selected `p` value
    /// # Examples
    /// ``
    ///   use a0kzg::{Poly, Scalar};
    ///   let mut p007 = Poly::zero();
    ///   p007.set(2, Scalar::from(7));
    ///   assert_eq!(p007, Poly::from(&[0, 0, 7]));
    ///  ```
    pub fn set(&mut self, i: usize, p: Scalar) {
        if i >= self.len() && p == Scalar::zero() {
            return;
        }

        fn new(v: &[Scalar], i: usize, p: Scalar) -> VecDeque<Scalar> {
            let mut v_new = VecDeque::new();
            v_new.reserve(v.len());
            v_new.reserve(i);
            v_new.extend(v);
            if v_new.len() <= i {
                v_new.resize(i + 1, Scalar::zero());
            }
            v_new[i] = p;
            v_new
        }

        *self = match (mem::replace(self, Self::Borrowed(&[])), i) {
            (Self::Borrowed(v), i) => Self::Allocated(new(v, i, p)),
            (Self::Owned(v), i) if i >= v.len() => Self::Allocated(new(&v, i, p)),
            (Self::Owned(mut v), i) => {
                v[i] = p;
                Self::Owned(v)
            }
            (Self::Allocated(mut v), i) => {
                if v.len() < i {
                    v.resize(i + 1, Scalar::zero());
                }
                v[i] = p;
                Self::Allocated(v)
            }
        }
        .normalize_self();
    }

    /// Returns the `i`-th coefficient
    /// # Examples
    /// ```
    ///   use a0kzg::{Poly, Scalar};
    ///   let mut p007 = Poly::zero();
    ///   p007.set(2, Scalar::from(7));
    ///   assert_eq!(p007.get(2), Some(&Scalar::from(7)));
    ///   assert_eq!(p007.get(3), None);
    ///  ```
    pub fn get(&self, i: usize) -> Option<&Scalar> {
        match self {
            Self::Borrowed(b) => b.get(i),
            Self::Owned(o) => o.get(i),
            Self::Allocated(a) => a.get(i),
        }
    }
}

impl<'a> fmt::Display for Poly<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first: bool = true;
        for i in (0..=self.degree()).rev() {
            let bi_n =
                num_bigint::BigUint::from_bytes_le(&self[i].to_bytes()).to_str_radix(10);
            let bi_inv =
                num_bigint::BigUint::from_bytes_le(&(-self[i]).to_bytes()).to_str_radix(10);

            if bi_n == "0" {
                continue;
            }

            if bi_inv.len() < 20 && bi_n.len() > 20 {
                if bi_inv == "1" && i != 0 {
                    write!(f, "-")?;
                } else {
                    write!(f, "-{}", bi_inv)?;
                }
            } else {
                if !first {
                    write!(f, "+")?;
                }
                if i == 0 || bi_n != "1" {
                    write!(f, "{}", bi_n)?;
                }
            }
            if i >= 1 {
                write!(f, "x")?;
            }
            if i >= 2 {
                write!(f, "^{}", i)?;
            }
            first = false;
        }
        Ok(())
    }
}

#[inline(always)]
fn add_helper<'a>(v: &mut VecDeque<Scalar>, mut o: impl Iterator<Item=Cow<'a, Scalar>>) {
    for lhs in v.iter_mut() {
        let Some(rhs) = o.next() else { return };
        *lhs += rhs.as_ref();
    }
    v.extend(o.map(Cow::into_owned));
}

#[inline(always)]
fn mac_helper<'a>(v: &mut VecDeque<Scalar>, mut o: impl Iterator<Item=impl Borrow<Scalar>>, s: &Scalar) {
    for lhs in v.iter_mut() {
        let Some(rhs) = o.next() else { return };
        *lhs += rhs.borrow() * s;
    }
    v.extend(o.map(|rhs| rhs.borrow() * s));
}

impl<'a> AddAssign<Poly<'a>> for Poly<'a> {
    fn add_assign(&mut self, rhs: Poly) {
        *self = match (replace(self, Poly::zero()), rhs) {
            (Self::Borrowed(ref lhs), Poly::Borrowed(rhs)) => if lhs.len() >= rhs.len() {
                let mut v = VecDeque::with_capacity(lhs.len());
                v.extend(*lhs);
                add_helper(&mut v, rhs.iter().map(Cow::Borrowed));
                Self::Allocated(v)
            } else {
                let mut v = VecDeque::with_capacity(rhs.len());
                v.extend(rhs);
                add_helper(&mut v, lhs.iter().map(Cow::Borrowed));
                Self::Allocated(v)
            },
            (Self::Borrowed(lhs), Poly::Owned(rhs)) if lhs.len() == 0 => Self::Owned(rhs),
            (Self::Borrowed(lhs), Poly::Owned(mut rhs)) if lhs.len() == 1 => {
                rhs[0] += lhs[0];
                Self::Owned(rhs)
            },
            (Self::Borrowed(lhs), Poly::Owned(rhs)) if lhs.len() >= rhs.len() => {
                let mut v = VecDeque::with_capacity(lhs.len());
                v.extend(lhs.iter().cloned());
                add_helper(&mut v, rhs.into_iter().map(Cow::Owned));
                Self::Allocated(v)
            },
            (Self::Borrowed(lhs), Poly::Owned(rhs)) => {
                let mut v = VecDeque::with_capacity(rhs.len());
                v.extend(rhs);
                add_helper(&mut v, lhs.iter().map(Cow::Borrowed));
                Self::Allocated(v)
            },
            (Self::Borrowed(lhs), Poly::Allocated(mut rhs)) => {
                add_helper(&mut rhs, lhs.iter().map(Cow::Borrowed));
                Self::Allocated(rhs)
            },

            (Self::Owned(lhs), Poly::Borrowed(rhs)) if rhs.len() == 0 => Self::Owned(lhs),
            (Self::Owned(mut lhs), Poly::Borrowed(rhs)) if rhs.len() == 1 => {
                lhs[0] += rhs[0];
                Self::Owned(lhs)
            },
            (Self::Owned(ref lhs), Poly::Borrowed(rhs)) if rhs.len() >= lhs.len() => {
                let mut v = VecDeque::with_capacity(rhs.len());
                v.extend(rhs.iter().cloned());
                add_helper(&mut v, rhs.iter().map(Cow::Borrowed));
                Self::Allocated(v)
            },
            (Self::Owned(ref lhs), Poly::Borrowed(rhs)) => {
                let mut v = VecDeque::with_capacity(lhs.len());
                v.extend(lhs);
                add_helper(&mut v, rhs.iter().map(Cow::Borrowed));
                Self::Allocated(v)
            },
            (Self::Owned(mut lhs), Poly::Owned(rhs)) => {
                lhs[0] += rhs[0];
                Self::Owned(lhs)
            },
            (Self::Owned(ref lhs), Poly::Allocated(mut rhs)) => {
                add_helper(&mut rhs, (*lhs).into_iter().map(Cow::Owned));
                Self::Allocated(rhs)
            },

            (Self::Allocated(mut lhs), Poly::Borrowed(rhs)) => {
                add_helper(&mut lhs, rhs.iter().map(Cow::Borrowed));
                Self::Allocated(lhs)
            },
            (Self::Allocated(mut lhs), Poly::Owned(rhs)) => {
                add_helper(&mut lhs, rhs.into_iter().map(Cow::Owned));
                Self::Allocated(lhs)
            },
            (Self::Allocated(mut lhs), Poly::Allocated(mut rhs)) => if lhs.len() >= rhs.len() {
                add_helper(&mut lhs, rhs.into_iter().map(Cow::Owned));
                Self::Allocated(lhs)
            } else {
                add_helper(&mut rhs, lhs.into_iter().map(Cow::Owned));
                Self::Allocated(rhs)
            },
        };
        self.normalize();
    }
}

impl<'a> AddAssign<&Poly<'a>> for Poly<'a> {
    fn add_assign(&mut self, rhs: &Poly) {
        for n in 0..rhs.len() {
            if n >= self.len() {
                self.push_back(rhs[n]);
            } else {
                self[n] += rhs[n];
            }
        }
        self.normalize();
    }
}

impl<'a> AddAssign<&Scalar> for Poly<'a> {
    fn add_assign(&mut self, rhs: &Scalar) {
        self[0] += rhs;
    }
}

impl<'a> SubAssign<&Poly<'a>> for Poly<'a> {
    fn sub_assign(&mut self, rhs: &Poly) {
        for n in 0..rhs.len() {
            if n >= self.len() {
                self.push_back(-rhs[n]);
            } else {
                self[n] -= rhs[n];
            }
        }
        self.normalize();
    }
}

impl<'a, 'b> Mul<&Poly<'b>> for &Poly<'a> {
    type Output = Poly<'a>;
    fn mul(self, rhs: &Poly<'b>) -> Self::Output {
        let mut mul = vec![Scalar::zero(); self.len() + rhs.len() - 1];
        for n in 0..self.len() {
            for m in 0..rhs.len() {
                mul[n + m] += self[n] * rhs[m];
            }
        }
        mul.into()
    }
}

impl<'a> Mul<&Scalar> for &Poly<'a> {
    type Output = Poly<'a>;
    fn mul(self, rhs: &Scalar) -> Self::Output {
        if rhs == &Scalar::zero() {
            Poly::zero()
        } else {
            self.iter().map(|v| v * rhs).collect::<VecDeque<_>>().into()
        }
    }
}

impl<'a> Mul<&Scalar> for Poly<'a> {
    type Output = Poly<'a>;
    fn mul(mut self, rhs: &Scalar) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<'a, 'b> MulAssign<&Poly<'b>> for Poly<'a> {
    fn mul_assign(&mut self, rhs: &Poly<'b>) {
        let v = self.to_vec_deque();
        let v_len = v.len();

        v.resize(v_len + rhs.len() - 1, Scalar::zero());
        for n in (0..v_len).rev() {
            for (m, m_v) in rhs.iter().enumerate().skip(v_len.saturating_sub(n)) {
                let tmp = v[n] * m_v;
                v[n + m] += tmp;
            }
        }
        for n in (0..v_len).rev() {
            v[n] *= rhs[0];
            for (m, m_v) in rhs.iter().enumerate().skip(1).take(n) {
                let tmp = v[n - m] * m_v;
                v[n] += tmp;
            }
        }
    }
}

impl<'a> MulAssign<&Scalar> for Poly<'a> {
    fn mul_assign(&mut self, rhs: &Scalar) {
        if rhs.is_zero_vartime() {
            let v = self.to_vec_deque();
            v.resize(1, Scalar::zero());
            v[0] = Scalar::zero();
        } else {
            for v in self.iter_mut() {
                *v *= rhs;
            }
        }
    }
}

impl<'a, 'b> Div<&Poly<'b>> for Poly<'a> {
    type Output = (Poly<'a>, Poly<'a>);
    fn div(self, rhs: &Poly<'b>) -> Self::Output {
        let (mut q, mut r) = (Poly::zero(), self);
        let i_lead_d = rhs[rhs.len() - 1].invert().unwrap();

        // calculates v -= rhs * t*x^i
        fn fused_sub_mul_assign(v: &mut Poly, rhs: &Poly, t: &Scalar, i: usize) {
            let t = -t;
            for n in 0..rhs.len() {
                let rhs = rhs[n] * t;
                let n = n + i;
                if n >= v.len() {
                    v.push_back(rhs);
                } else {
                    v[n] += rhs;
                }
            }
            v.normalize();
        }

        while !r.is_zero() && r.degree() >= rhs.degree() {
            let lead_r = r[r.len() - 1];
            let lead = lead_r * i_lead_d;
            let i = r.len() - rhs.len();

            q.set(i, match q.get(i) {
               None => lead,
               Some(q) => q + lead, 
            });

            fused_sub_mul_assign(&mut r, &rhs, &lead, i);
        }
        (q, r)
    }
}

impl<'a> Div for Poly<'a> {
    type Output = (Poly<'a>, Poly<'a>);

    fn div(self, rhs: Poly<'a>) -> Self::Output {
        self / &rhs
    }
}

impl<'a> Index<usize> for Poly<'a> {
    type Output = Scalar;
    fn index(&self, i: usize) -> &Scalar {
        match self {
            Self::Borrowed(b) => &b[i],
            Self::Owned(o) => &o[i],
            Self::Allocated(a) => &a[i],
        }
    }
}
impl<'a> IndexMut<usize> for Poly<'a> {
    fn index_mut(&mut self, i: usize) -> &mut Scalar {
        match self {
            Self::Borrowed(borrowed) => {
                let mut new = VecDeque::with_capacity(borrowed.len());
                new.extend(*borrowed);
                *self = Self::Allocated(new);
                match *self {
                    Self::Allocated(ref mut a) => &mut a[i],
                    _ => unreachable!(),
                }
            },
            Self::Owned(o) => &mut o[i],
            Self::Allocated(a) => &mut a[i],
        }
    }
}

#[cfg(test)]
mod test {
    use std::collections::VecDeque;

    use ff::Field;

    use super::Poly;

    type Scalar = bls12_381::Scalar<0, true>;

    #[test]
    fn test_poly_add() {
        let mut p246 = Poly::from(&[1, 2, 3]);
        p246 += &Poly::from(&[1, 2, 3]);
        assert_eq!(p246, Poly::from(&[2, 4, 6]));

        let mut p24645 = Poly::from(&[1, 2, 3]);
        p24645 += &Poly::from(&[1, 2, 3, 4, 5]);
        assert_eq!(p24645, Poly::from(&[2, 4, 6, 4, 5]));

        let mut p24646 = Poly::from(&[1, 2, 3, 4, 6]);
        p24646 += &Poly::from(&[1, 2, 3]);
        assert_eq!(p24646, Poly::from(&[2, 4, 6, 4, 6]));
    }

    #[test]
    fn test_poly_sub() {
        let mut p0 = Poly::from(&[1, 2, 3]);
        p0 -= &Poly::from(&[1, 2, 3]);
        assert_eq!(p0, Poly::from(&[0]));

        let mut p003 = Poly::from(&[1, 2, 3]);
        p003 -= &Poly::from(&[1, 2]);
        assert_eq!(p003, Poly::from(&[0, 0, 3]));
    }

    #[test]
    fn test_poly_mul() {
        let mut p = Poly::from(&[5, 0, 10, 6]);
        assert_eq!(
            &p * &Poly::from(&[1, 2, 4]),
            Poly::from(&[5, 10, 30, 26, 52, 24])
        );

        p *= &Poly::from(&[1, 2, 4]);
        assert_eq!(p, Poly::from(&[5, 10, 30, 26, 52, 24]));

        let mut p = Poly::from(&[1, 2, 4]);
        p *= &Poly::from(&[5, 0, 10, 6]);
        assert_eq!(p, Poly::from(&[5, 10, 30, 26, 52, 24]));


        let q = &p * &Poly::from(&[3, 1]);
        Poly::mul_by_x_sub_s(p.to_vec_deque(), &-Scalar::from(3));
        assert_eq!(p, q);
    }




    #[test]
    fn test_poly_set() {
        let mut p = Poly::from(&[5, 0, 10, 6]);
        p.set(0, Scalar::zero());
        assert_eq!(p, Poly::from(&[0, 0, 10, 6]));
        p.set(2, Scalar::zero());
        assert_eq!(p, Poly::from(&[0, 0, 0, 6]));
        p.set(3, Scalar::zero());
        assert_eq!(p, Poly::zero(),);
        p.set(4, Scalar::one());
        assert_eq!(p, Poly::from(&[0, 0, 0, 0, 1]));
    }

    #[test]
    fn test_div() {
        fn do_test(n: Poly, d: Poly) {
            let (q, r) = n.clone() / d.clone();
            let mut n2 = &q * &d;
            n2 += &r;
            assert_eq!(n, n2);
        }

        do_test(Poly::from(&[1]), Poly::from(&[1, 1]));
        do_test(Poly::from(&[1, 1]), Poly::from(&[1, 1]));
        do_test(Poly::from(&[1, 2, 1]), Poly::from(&[1, 1]));
        do_test(
            Poly::from(&[1, 2, 1, 2, 5, 8, 1, 9]),
            Poly::from(&[1, 1, 5, 4]),
        );
    }

    #[test]
    fn test_print() {
        assert_eq!("x^2+2x+1", format!("{}", Poly::from(&[1, 2, 1])));
        assert_eq!("x^2+1", format!("{}", Poly::from(&[1, 0, 1])));
        assert_eq!("x^2", format!("{}", Poly::from(&[0, 0, 1])));
        assert_eq!("2x^2", format!("{}", Poly::from(&[0, 0, 2])));
        assert_eq!("-4", format!("{}", Poly::new([-Scalar::from(4)])));
        assert_eq!(
            "-4x",
            format!("{}", Poly::new(&[Scalar::zero(), -Scalar::from(4)]))
        );
        assert_eq!(
            "-x-2",
            format!("{}", Poly::new(&[-Scalar::from(2), -Scalar::from(1)]))
        );
        assert_eq!(
            "x-2",
            format!("{}", Poly::new(&[-Scalar::from(2), Scalar::from(1)]))
        );
    }

    #[test]
    fn test_lagrange() {
        let points = [
            (Scalar::from(12342), Scalar::from(22342)),
            (Scalar::from(2234), Scalar::from(22222)),
            (Scalar::from(3982394), Scalar::from(111114)),
            (Scalar::from(483838), Scalar::from(444444)),
        ];
        let l = Poly::lagrange(&points);
        points.iter().for_each(|p| assert_eq!(l.eval(&p.0), p.1));
        let l = Poly::lagrange2(&points);
        points.iter().for_each(|p| assert_eq!(l.eval(&p.0), p.1));

        let points = [
            (Scalar::from(12342), Scalar::from(22342)),
        ];
        let l = Poly::lagrange(&points);
        points.iter().for_each(|p| assert_eq!(l.eval(&p.0), p.1));
        let l = Poly::lagrange2(&points);
        points.iter().for_each(|p| assert_eq!(l.eval(&p.0), p.1));
    }

    #[test]
    fn test_z_poly_of() {
        let points = [
            (Scalar::from(2), Scalar::from(22342)),
            (Scalar::from(3), Scalar::from(22222)),
            (Scalar::from(5), Scalar::from(111114)),
            (Scalar::from(7), Scalar::from(444444)),
        ];
        let l = Poly::z_poly_of(&points);
        points.iter().for_each(|p| assert_eq!(l.eval(&p.0), Scalar::zero()));
    }

    #[test]
    fn test_div_by_x_plus_s() {
        let scalars = (0..1025)
            .map(|_| Scalar::random(rand::thread_rng()))
            .collect::<Vec<_>>();

        let mut p = VecDeque::new();
        p.push_back(Scalar::one());
        for s in scalars {
            let old_p = p.clone();
            Poly::mul_by_x_sub_s(&mut p, &s);
            assert_eq!(old_p, Poly::div_by_x_plus_s(p.clone(), &-s))
        }
    }

}
