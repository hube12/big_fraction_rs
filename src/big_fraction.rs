use num_bigint::{BigInt, ParseBigIntError, BigUint};
use std::ops::{Neg, Div, Not, Add, Mul};
use num_traits::{Signed, Zero, One, ToPrimitive, Num};
use num_integer::Integer;
use core::{hash, fmt};
use std::cmp::Ordering;
use std::str::FromStr;
use std::error::Error;
use std::convert::TryFrom;

#[derive(Debug)]
pub struct BigFraction {
    ntor: BigInt,
    dtor: BigInt,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseBigFractionError {
    kind: BigFractionErrorKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum BigFractionErrorKind {
    Empty,
    InvalidDigit,
    DivideByZero,
}

impl ParseBigFractionError {
    fn __description(&self) -> &str {
        use self::BigFractionErrorKind::*;
        match self.kind {
            Empty => "cannot parse integer from empty string",
            InvalidDigit => "invalid digit found in string",
            DivideByZero => "Dividing by zero"
        }
    }

    fn empty() -> Self {
        ParseBigFractionError {
            kind: BigFractionErrorKind::Empty,
        }
    }

    fn invalid() -> Self {
        ParseBigFractionError {
            kind: BigFractionErrorKind::InvalidDigit,
        }
    }
    fn divide_by_zero() -> Self {
        ParseBigFractionError {
            kind: BigFractionErrorKind::DivideByZero,
        }
    }
}

impl fmt::Display for ParseBigFractionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.__description().fmt(f)
    }
}

#[cfg(feature = "std")]
impl Error for ParseBigFractionError {
    fn description(&self) -> &str {
        self.__description()
    }
}

impl Clone for BigFraction {
    #[inline]
    fn clone(&self) -> Self {
        BigFraction {
            ntor: self.ntor.clone(),
            dtor: self.dtor.clone(),
        }
    }

    #[inline]
    fn clone_from(&mut self, other: &Self) {
        self.ntor.clone_from(&other.ntor);
        self.dtor.clone_from(&other.dtor);
    }
}

impl hash::Hash for BigFraction {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.ntor.hash(state);
        self.dtor.hash(state);
    }
}


impl PartialEq for BigFraction {
    #[inline]
    fn eq(&self, other: &BigFraction) -> bool {
        self.get_denominator().eq(&other.get_denominator()) && self.get_numerator().eq(&other.get_numerator())
    }
}

impl Eq for BigFraction {}

impl PartialOrd for BigFraction {
    #[inline]
    fn partial_cmp(&self, other: &BigFraction) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BigFraction {
    #[inline]
    fn cmp(&self, other: &BigFraction) -> Ordering {
        (self.get_numerator() * other.get_denominator()).cmp(&(self.get_denominator() * other.get_numerator()))
    }
}


impl Default for BigFraction {
    #[inline]
    fn default() -> BigFraction {
        Zero::zero()
    }
}


impl fmt::Display for BigFraction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let radix: u32 = 10;
        if self.dtor.eq(&One::one()) {
            return f.pad_integral(!self.is_negative(), "", &self.ntor.to_str_radix(radix));
        }
        f.pad_integral(!self.is_negative(), "", &*(self.ntor.to_str_radix(radix) + "/" + &*self.dtor.to_str_radix(radix)))
    }
}

impl fmt::Binary for BigFraction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let radix: u32 = 2;
        if self.dtor.eq(&One::one()) {
            return f.pad_integral(!self.is_negative(), "0b", &self.ntor.to_str_radix(radix));
        }
        f.pad_integral(!self.is_negative(), "0b", &*(self.ntor.to_str_radix(radix) + "/" + &*self.dtor.to_str_radix(radix)))
    }
}

impl fmt::Octal for BigFraction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let radix: u32 = 8;
        if self.dtor.eq(&One::one()) {
            return f.pad_integral(!self.is_negative(), "0o", &self.ntor.to_str_radix(radix));
        }
        f.pad_integral(!self.is_negative(), "0o", &*(self.ntor.to_str_radix(radix) + "/" + &*self.dtor.to_str_radix(radix)))
    }
}

impl fmt::LowerHex for BigFraction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let radix: u32 = 16;
        if self.dtor.eq(&One::one()) {
            return f.pad_integral(!self.is_negative(), "0x", &self.ntor.to_str_radix(radix));
        }
        f.pad_integral(!self.is_negative(), "0x", &*(self.ntor.to_str_radix(radix) + "/" + &*self.dtor.to_str_radix(radix)))
    }
}

impl fmt::UpperHex for BigFraction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let radix: u32 = 16;
        if self.dtor.eq(&One::one()) {
            let mut s = self.ntor.to_str_radix(radix);
            s.make_ascii_uppercase();
            return f.pad_integral(!self.is_negative(), "0x", &s);
        }
        let mut s1 = self.ntor.to_str_radix(radix);
        s1.make_ascii_uppercase();
        let mut s2 = self.dtor.to_str_radix(radix);
        s2.make_ascii_uppercase();
        f.pad_integral(!self.is_negative(), "0x", &*(s1 + "/" + &*s2))
    }
}

impl Not for BigFraction {
    type Output = BigFraction;

    fn not(mut self) -> BigFraction {
        self = BigFraction::simplify(self);
        self.ntor.neg();
        self
    }
}

impl FromStr for BigFraction {
    type Err = ParseBigFractionError;

    #[inline]
    fn from_str(s: &str) -> Result<BigFraction, ParseBigFractionError> {
        BigFraction::from_str_radix(s, 10)
    }
}

impl Num for BigFraction {
    type FromStrRadixErr = ParseBigFractionError;

    /// Creates and initializes a BigInt.
    #[inline]
    fn from_str_radix(mut s: &str, radix: u32) -> Result<BigFraction, ParseBigFractionError> {
        let mut it = s.split("/");
        if let Some(ntor) = it.next() {
            let r: Result<BigInt, ParseBigIntError> = BigInt::from_str_radix(ntor, 10);
            let hi: BigInt;
            if r.is_ok() {
                hi = r.unwrap()
            } else {
                return Err(r.unwrap_err().into());
            }
            let mut lo: BigInt = One::one();
            if let Some(dtor) = it.next() {
                let r: Result<BigInt, ParseBigIntError> = BigInt::from_str_radix(dtor, 10);
                if r.is_ok() {
                    lo = r.unwrap()
                } else {
                    return Err(r.unwrap_err().into());
                }
            }
            return BigFraction::new(hi, lo);
        } else {
            Err(ParseBigFractionError::empty())
        }
    }
}


impl Zero for BigFraction {
    #[inline]
    fn zero() -> BigFraction {
        BigFraction {
            ntor: BigInt::zero(),
            dtor: BigInt::one(),
        }
    }

    #[inline]
    fn set_zero(&mut self) {
        self.ntor.set_zero();
        self.dtor.set_one();
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.ntor.is_zero()
    }
}

impl One for BigFraction {
    #[inline]
    fn one() -> BigFraction {
        BigFraction {
            ntor: BigInt::one(),
            dtor: BigInt::one(),
        }
    }

    #[inline]
    fn set_one(&mut self) {
        self.ntor.set_one();
        self.dtor.set_one();
    }

    #[inline]
    fn is_one(&self) -> bool {
        let temp:BigFraction =BigFraction::simplify(self.clone());
        temp.dtor.is_one() && temp.ntor.is_one()
    }
}


impl Signed for BigFraction {
    #[inline]
    fn abs(&self) -> BigFraction {
        let hi = self.ntor.abs();
        let lo = self.dtor.abs();
        BigFraction::new(hi, lo).expect("This case is not possible")
    }

    #[inline]
    fn abs_sub(&self, other: &BigFraction) -> BigFraction {
        if *self <= *other {
            Zero::zero()
        } else {
            self - other
        }
    }

    #[inline]
    fn signum(&self) -> BigInt {
        self.dtor.signum()
    }

    #[inline]
    fn is_positive(&self) -> bool {
        self.signum()>BigInt::zero()
    }

    #[inline]
    fn is_negative(&self) -> bool {
        self.signum()<BigInt::zero()
    }
}

impl<'a, 'b> Add<&'b BigFraction> for &'a BigFraction {
    type Output = BigFraction;

    #[inline]
    fn add(self, other: &BigFraction) -> BigFraction {
        let hi=self.ntor.mul(&other.dtor).add(other.dtor.mul(&self.dtor));
        let lo=self.dtor.mul(&other.dtor);
        return BigFraction::new(hi,lo).expect("An error occured while adding");
    }
}

impl<'a, 'b> Add<&'b BigInt> for &'a BigFraction {
    type Output = BigFraction;

    #[inline]
    fn add(self, other: &BigInt) -> BigFraction {
        let hi=self.ntor.add(other.mul(&self.dtor));
        let lo=self.dtor.clone();
        return BigFraction::new(hi,lo).expect("An error occured while adding");
    }
}

/// A generic trait for converting a value to a `BigInt`. This may return
/// `None` when converting from `f32` or `f64`, and will always succeed
/// when converting from any integer or unsigned primitive, or `BigUint`.
pub trait ToBigFraction {
    /// Converts the value of `self` to a `BigInt`.
    fn to_bigfraction(&self) -> Option<BigFraction>;
}

impl ToBigFraction for BigFraction {
    #[inline]
    fn to_bigfraction(&self) -> Option<BigFraction> {
        Some(self.clone())
    }
}

impl ToBigFraction for BigUint {
    #[inline]
    fn to_bigfraction(&self) -> Option<BigFraction> {
        // TODO
        if self.is_zero() {
            Some(Zero::zero())
        } else {
            Some(BigInt {
                sign: Plus,
                data: self.clone(),
            })
        }
    }
}

impl biguint::ToBigUint for BigFraction {
    #[inline]
    fn to_biguint(&self) -> Option<BigUint> {
        // TODO
        match self.sign() {
            Plus => Some(self.data.clone()),
            NoSign => Some(Zero::zero()),
            Minus => None,
        }
    }
}

#[cfg(has_try_from)]
impl TryFrom<&BigInt> for BigUint {
    type Error = TryFromBigIntError<()>;

    #[inline]
    fn try_from(value: &BigInt) -> Result<BigUint, TryFromBigIntError<()>> {
        value.to_biguint().ok_or(TryFromBigIntError::new(()))
    }
}

#[cfg(has_try_from)]
impl TryFrom<BigFraction> for BigInt {
    type Error = TryFromBigIntError<BigInt>;

    #[inline]
    fn try_from(value: BigInt) -> Result<BigUint, TryFromBigIntError<BigInt>> {
        if value.sign() == Sign::Minus {
            Err(TryFromBigIntError::new(value))
        } else {
            Ok(value.data)
        }
    }
}


macro_rules! impl_to_bigfraction {
    ($T:ty, $from_ty:path) => {
        impl ToBigFraction for $T {
            #[inline]
            fn to_bigfraction(&self) -> Option<BigFraction> {
                $from_ty(*self)
            }
        }
    };
}

impl_to_bigfraction!(isize, FromPrimitive::from_isize);
impl_to_bigfraction!(i8, FromPrimitive::from_i8);
impl_to_bigfraction!(i16, FromPrimitive::from_i16);
impl_to_bigfraction!(i32, FromPrimitive::from_i32);
impl_to_bigfraction!(i64, FromPrimitive::from_i64);
impl_to_bigfraction!(i128, FromPrimitive::from_i128);

impl_to_bigfraction!(usize, FromPrimitive::from_usize);
impl_to_bigfraction!(u8, FromPrimitive::from_u8);
impl_to_bigfraction!(u16, FromPrimitive::from_u16);
impl_to_bigfraction!(u32, FromPrimitive::from_u32);
impl_to_bigfraction!(u64, FromPrimitive::from_u64);
impl_to_bigfraction!(u128, FromPrimitive::from_u128);

impl_to_bigfraction!(f32, FromPrimitive::from_f32);
impl_to_bigfraction!(f64, FromPrimitive::from_f64);


impl<'a> BigFraction {
    pub fn new(numerator: BigInt, denominator: BigInt) -> Result<Self, ParseBigFractionError> {
        if denominator.signum() == BigInt::zero() {
            Err(ParseBigFractionError::divide_by_zero())
        } else {
            Ok(Self::simplify(BigFraction { ntor: numerator.clone(), dtor: denominator.clone() }))
        }
    }

    pub fn new_integer(numerator: BigInt) -> Result<Self, ParseBigFractionError> {
        Self::new(numerator, One::one())
    }

    pub fn parse(s: String) -> Option<BigInt> {
        // TODO FIXME
        BigInt::parse_bytes(&*s.into_bytes(), 10)
    }

    pub fn get_denominator(&self) -> BigInt {
        self.dtor.clone()
    }

    pub fn get_numerator(&self) -> BigInt {
        self.ntor.clone()
    }

    pub fn to_double(&self) -> f64 {
        self.ntor.to_f64().expect("no numerator") / self.dtor.to_f64().expect("no denominator")
    }

    pub fn simplify(mut fraction: BigFraction) -> BigFraction {
        if fraction.ntor.signum() == BigInt::zero() {
            fraction.dtor = BigInt::one();
            return fraction;
        }
        if fraction.dtor.signum() == -BigInt::one() {
            fraction.ntor = (&fraction.ntor).neg();
            fraction.dtor = (&fraction.dtor).neg();
        }
        let common_factor: BigInt = fraction.ntor.gcd(&fraction.dtor);
        fraction.ntor = (&fraction.ntor).div(&common_factor);
        fraction.dtor = (&fraction.dtor).div(&common_factor);
        fraction
    }
}