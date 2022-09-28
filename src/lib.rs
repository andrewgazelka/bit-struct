#![doc = include_str!("../README.md")]
#![no_std]

use core::{
    cmp::Ordering,
    fmt::{Debug, Display, Formatter},
    marker::PhantomData,
    ops::{
        Add, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, Mul, Rem, Shl,
        ShlAssign, Shr, ShrAssign, Sub,
    },
};

use num_traits::{Bounded, Num, One, Zero};
/// Import serde here so we can reference it inside macros
#[doc(hidden)]
pub use serde;
use serde::{Deserializer, Serializer};

/// [`UnsafeStorage`] is used to mark that there are some arbitrary invariants
/// which must be maintained in storing its inner value. Therefore, creation and
/// modifying of the inner value is an "unsafe" behavior. Although it might not
/// be unsafe in traditional Rust terms (no memory unsafety), behavior might be
/// "undefined"—or at least undocumented, because invariants are expected to be
/// upheld.
///
/// This is useful in macros which do not encapsulate their storage in modules.
/// This makes the macros for the end-user more ergonomic, as they can use the
/// macro multiple times in a single module.
#[repr(transparent)]
#[derive(Copy, Clone, PartialOrd, PartialEq, Eq, Ord, Hash, Default)]
pub struct UnsafeStorage<T>(T);

impl<T> UnsafeStorage<T> {
    /// Create a new `UnsafeStorage` with the given inner value.
    ///
    /// # Safety
    /// - See the broader scope that this is called in and which invariants are
    ///   mentioned
    pub const unsafe fn new_unsafe(inner: T) -> Self {
        Self(inner)
    }

    /// Mutably access the value stored inside
    ///
    /// # Safety
    /// This should be a safe operation assuming that when modifying T to T',
    /// `UnsafeStorage::new_unsafe`(T') is safe
    pub unsafe fn as_ref_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

impl<T> AsRef<T> for UnsafeStorage<T> {
    /// Access the value stored inside
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T: Copy> UnsafeStorage<T> {
    /// Access the value stored inside
    pub const fn inner(&self) -> T {
        self.0
    }
}

/// A struct which allows for getting/setting a given property
pub struct GetSet<'a, P, T, const START: usize, const STOP: usize> {
    /// The referenced bitfield type.
    parent: &'a mut P,
    /// The type in the get/set operations
    _phantom: PhantomData<T>,
}

impl<'a, P, T, const START: usize, const STOP: usize> GetSet<'a, P, T, START, STOP> {
    /// The bit offset at which this `GetSet` instance starts
    pub const fn start(&self) -> usize {
        START
    }

    /// The bit offset at which this `GetSet` instance ends
    pub const fn stop(&self) -> usize {
        STOP
    }
}

/// A trait which defines how many bits are needed to store a struct.
///
/// # Safety
/// Define `Num` as `{i,u}{8,16,32,64,128}`.
/// - when calling `core::mem::transmute` on `Self`, only bits [0, COUNT) can be
///   non-zero
/// - `TryFrom<Num>` produces `Some(x)` <=> `core::mem::transmute(num)` produces
///   a valid Self(x)
/// - `TryFrom<Num>` produces `None` <=> `core::mem::transmute(num)` produces an
///   invalid state for Self
pub unsafe trait BitCount {
    /// The number of bits associated with this type
    const COUNT: usize;
}

/// Implement the [`BitCount`] trait easily for the built-in base types
macro_rules! bit_counts {
    ($($num: ty = $count: literal),*) => {
        $(
        // Safety:
        // This is correct for the built-in types
        unsafe impl BitCount for $num {
            const COUNT: usize = $count;
        }
        )*
    };
}

bit_counts!(u8 = 8, u16 = 16, u32 = 32, u64 = 64, u128 = 128, bool = 1);

/// Assert that the given type is valid for any representation thereof
macro_rules! always_valid {
    ($($elem: ty),*) => {
        $(
        // Safety:
        // This is correct: stdlib types are always valid
        unsafe impl <P> ValidCheck<P> for $elem {
            const ALWAYS_VALID: bool = true;
        }
        )*
    };
}

always_valid!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, bool);

impl u1 {
    /// The 1-bit representation of true (1)
    pub const TRUE: Self = Self(1);
    /// The 1-bit representation of false (0)
    pub const FALSE: Self = Self(0);

    /// Get the opposite of this value (i.e. `TRUE` <--> `FALSE`)
    #[must_use]
    pub const fn toggle(self) -> Self {
        match self {
            Self::FALSE => Self::TRUE,
            _ => Self::FALSE,
        }
    }
}

/// A type which can be a field of a `bit_struct`
pub trait FieldStorage {
    /// The type this field stores as
    type StoredType;
    /// Get the raw representation of this value
    fn inner_raw(self) -> Self::StoredType;
}
/// Implement the [`FieldStorage`] trait for some built-in types
macro_rules! impl_field_storage {
    ($(($type:ty, $base:ty)),+ $(,)?) => {
        $(
        impl FieldStorage for $type {
            type StoredType = $base;

            fn inner_raw(self) -> Self::StoredType {
                self.into()
            }
        }
        )+
    };
}
impl_field_storage!(
    (bool, u8),
    (u8, Self),
    (u16, Self),
    (u32, Self),
    (u64, Self),
    (u128, Self),
);

/// Create a type for representing signed integers of sizes not provided by rust
macro_rules! new_signed_types {
    (
        $($name: ident($count: literal, $inner: ty, $signed: ty)),*
    ) => {
        $(

        #[doc = concat!("An unsigned integer which contains ", stringify!($count), "bits")]
        #[allow(non_camel_case_types)]
        #[derive(Copy, Clone, Eq, PartialEq, Hash)]
        pub struct $name($inner);

        always_valid!($name);

        impl serde::Serialize for $name {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                self.value().serialize(serializer)
            }
        }

        impl <'de> serde::Deserialize<'de> for $name {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                let inner = <$signed>::deserialize(deserializer)?;
                $name::new(inner).ok_or(serde::de::Error::custom("invalid size"))
            }
        }

        impl PartialOrd for $name {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                self.value().partial_cmp(&other.value())
            }
        }

        impl Ord for $name {
            fn cmp(&self, other: &Self) -> Ordering {
                self.value().cmp(&other.value())
            }
        }

        impl Debug for $name {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                f.write_fmt(format_args!("{}", self.value()))
            }
        }

        impl Display for $name {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                f.write_fmt(format_args!("{}", self.value()))
            }
        }

        #[doc = concat!("Produce a value of type ", stringify!($name))]
        ///
        /// This macro checks at compile-time that it fits. To check at run-time see the
        #[doc = concat!("[`", stringify!($name), "::new`] function.")]
        #[macro_export]
        macro_rules! $name {
            ($value: expr) => {
                {
                    const VALUE: $signed = $value;
                    const _: () = assert!(VALUE <= $crate::$name::MAX, "The provided value is too large");
                    const _: () = assert!(VALUE >= $crate::$name::MIN, "The provided value is too small");
                    let res: $name = unsafe {$crate::$name::new_unchecked(VALUE)};
                    res
                }
            };
        }

        // Safety:
        // This is guaranteed to be the correct arguments
        unsafe impl BitCount for $name {
            const COUNT: usize = $count;
        }

        num_traits!($name, $signed);

        impl $name {
            /// Create a new $name from value
            /// # Safety
            /// - value must fit within the number of bits defined in the type
            pub const unsafe fn new_unchecked(value: $signed) -> Self {
                let unsigned_value = value as $inner;
                if value >= 0 {
                    Self(unsigned_value)
                } else {
                    // we can do this
                    let value = unsigned_value & Self::MAX_UNSIGNED;
                    Self(value | Self::POLARITY_FLAG)
                }
            }


            /// Create a new $name from value
            /// # Safety
            /// - value must fit within the number of bits defined in the type
            pub fn new(value: $signed) -> Option<Self> {
                if (Self::MIN..=Self::MAX).contains(&value) {
                    // SAFETY:
                    // We've just checked that this is safe to call
                    Some(unsafe {Self::new_unchecked(value)})
                } else {
                    None
                }
            }

            const POLARITY_FLAG: $inner = (1 << ($count - 1));
            const MAX_UNSIGNED: $inner = (1 << ($count-1)) - 1;
            /// The largest value this type can hold
            pub const MAX: $signed = Self::MAX_UNSIGNED as $signed;
            /// The smallest value this type can hold
            pub const MIN: $signed = -(Self::MAX_UNSIGNED as $signed) - 1;

            /// Get the value stored in here, as a signed integer
            pub const fn value(self) -> $signed {
                match self.0 >> ($count - 1) {
                    0 => self.0 as $signed,
                    _ => {
                        // 0's out negative
                        let rem = self.0 ^ Self::POLARITY_FLAG;
                        let amount = Self::MAX_UNSIGNED - rem;
                        -(amount as $signed) - 1
                    }
                }
            }
        }

        impl Default for $name {
            fn default() -> Self {
                Self(0)
            }
        }

        impl FieldStorage for $name {
            type StoredType = $inner;

            fn inner_raw(self) -> Self::StoredType {
                self.0
            }
        }
        )*
    };
}

/// Implement traits from the [`num_traits`] crate for our new number types
macro_rules! num_traits {
    ($num:ident, $super_kind:ty) => {
        impl Zero for $num {
            fn zero() -> Self {
                $num::new(0).unwrap()
            }

            fn is_zero(&self) -> bool {
                self.0 == 0
            }
        }

        impl Add for $num {
            type Output = Self;

            fn add(self, rhs: Self) -> Self::Output {
                $num::new(self.value() + rhs.value()).unwrap()
            }
        }

        impl One for $num {
            fn one() -> Self {
                $num::new(1).unwrap()
            }
        }

        impl Mul for $num {
            type Output = Self;

            fn mul(self, rhs: Self) -> Self::Output {
                $num::new(self.value() * rhs.value()).unwrap()
            }
        }

        impl Sub for $num {
            type Output = $num;

            fn sub(self, rhs: Self) -> Self::Output {
                $num::new(self.value() - rhs.value()).unwrap()
            }
        }

        impl Div for $num {
            type Output = Self;

            fn div(self, rhs: Self) -> Self::Output {
                $num::new(self.value() / rhs.value()).unwrap()
            }
        }

        impl Rem for $num {
            type Output = Self;

            fn rem(self, rhs: Self) -> Self::Output {
                $num::new(self.value() % rhs.value()).unwrap()
            }
        }

        impl Num for $num {
            type FromStrRadixErr = ();

            fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
                let parse = <$super_kind>::from_str_radix(str, radix).map_err(|_| ())?;
                $num::new(parse).ok_or(())
            }
        }

        impl core::str::FromStr for $num {
            type Err = <Self as Num>::FromStrRadixErr;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                <Self as Num>::from_str_radix(s, 10)
            }
        }

        impl Shr<usize> for $num {
            type Output = $num;

            fn shr(self, rhs: usize) -> Self::Output {
                $num::new(self.value() >> rhs).unwrap()
            }
        }

        impl Shl<usize> for $num {
            type Output = $num;

            fn shl(self, rhs: usize) -> Self::Output {
                $num::new(self.value() << rhs).unwrap()
            }
        }

        impl ShrAssign<usize> for $num {
            fn shr_assign(&mut self, rhs: usize) {
                let got = *self >> rhs;
                *self = got;
            }
        }

        impl ShlAssign<usize> for $num {
            fn shl_assign(&mut self, rhs: usize) {
                let got = *self << rhs;
                *self = got;
            }
        }

        impl Bounded for $num {
            fn min_value() -> Self {
                $num::new(Self::MIN).unwrap()
            }

            fn max_value() -> Self {
                $num::new(Self::MAX).unwrap()
            }
        }

        impl BitAnd for $num {
            type Output = $num;

            fn bitand(self, rhs: Self) -> Self::Output {
                $num(self.0 & rhs.0)
            }
        }

        impl BitXor for $num {
            type Output = $num;

            fn bitxor(self, rhs: Self) -> Self::Output {
                $num(self.0 ^ rhs.0)
            }
        }

        impl BitXorAssign for $num {
            fn bitxor_assign(&mut self, rhs: Self) {
                self.0 ^= rhs.0
            }
        }

        impl BitAndAssign for $num {
            fn bitand_assign(&mut self, rhs: Self) {
                self.0 &= rhs.0
            }
        }

        impl BitOr for $num {
            type Output = Self;

            fn bitor(self, rhs: Self) -> Self::Output {
                $num(self.0 | rhs.0)
            }
        }

        impl BitOrAssign for $num {
            fn bitor_assign(&mut self, rhs: Self) {
                self.0 |= rhs.0;
            }
        }
    };
}

/// Create a type for representing unsigned integers of sizes not provided by
/// rust
macro_rules! new_unsigned_types {
    (
        $($name: ident($count: literal, $inner: ty)),*
    ) => {
        $(

        #[doc = concat!("An unsigned integer which contains ", stringify!($count), "bits")]
        #[allow(non_camel_case_types)]
        #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
        pub struct $name($inner);

        always_valid!($name);

        impl Debug for $name {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                f.write_fmt(format_args!("{}", self.0))
            }
        }

        impl Display for $name {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                f.write_fmt(format_args!("{}", self.0))
            }
        }

        impl serde::Serialize for $name {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                self.value().serialize(serializer)
            }
        }

        impl <'de> serde::Deserialize<'de> for $name {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                let inner = <$inner>::deserialize(deserializer)?;
                $name::new(inner).ok_or(serde::de::Error::custom("invalid size"))
            }
        }

        #[doc = concat!("Produce a value of type ", stringify!($name))]
        ///
        /// This macro checks at compile-time that it fits. To check at run-time see the
        #[doc = concat!("[`", stringify!($name), "::new`] function.")]
        #[macro_export]
        macro_rules! $name {
            ($value: literal) => {
                {
                    const VALUE: $inner = $value;

                    // this is always valid because we have one more bit than we need in $inner
                    // type
                    const _: () = assert!($crate::$name::MAX >= VALUE, "The provided value is too large");
                    unsafe {$crate::$name::new_unchecked(VALUE)}
                }
            };
        }


        // SAFETY:
        // This is correct (guaranteed by macro arguments)
        unsafe impl BitCount for $name {
            /// The number of bits this type takes up
            ///
            /// Note that this is the conceptual amount it needs in a bit struct, not the amount it
            /// will use as its own variable on the stack.
            const COUNT: usize = $count;
        }

        impl $name {
            /// The largest value that can be stored
            pub const MAX: $inner = (1 << ($count)) - 1;
            /// The smallest value that can be stored
            pub const MIN: $inner = 0;

            #[doc = concat!("Create a new ", stringify!($name), " from an inner value")]
            ///
            /// This method does not do any checks that the value passed is valid. To check that,
            #[doc = concat!("use the [`", stringify!($name), "::new`] function.")]
            ///
            /// # Safety
            /// The value must be valid value of the given type.
            pub const unsafe fn new_unchecked(value: $inner) -> Self {
                Self(value)
            }

            #[doc = concat!("Create a new ", stringify!($name), " from an inner value")]
            ///
            /// This method checks that the inner value is valid, and return `None` if it isn't.
            pub fn new(value: $inner) -> Option<Self> {
                if (Self::MIN..=Self::MAX).contains(&value) {
                    // SAFETY:
                    // We've checked that this is safe to do in the above `if`
                    Some(unsafe {Self::new_unchecked(value)})
                } else {
                    None
                }
            }

            /// Get the stored value
            pub const fn value(self) -> $inner {
                self.0
            }
        }

        impl Default for $name {
            fn default() -> Self {
                Self(0)
            }
        }

        num_traits!($name, $inner);

        impl FieldStorage for $name {
            type StoredType = $inner;

            fn inner_raw(self) -> Self::StoredType {
                self.0
            }
        }
        )*
    };
}

new_signed_types!(
    i2(2, u8, i8),
    i3(3, u8, i8),
    i4(4, u8, i8),
    i5(5, u8, i8),
    i6(6, u8, i8),
    i7(7, u8, i8),
    i9(9, u16, i16),
    i10(10, u16, i16),
    i11(11, u16, i16),
    i12(12, u16, i16),
    i13(13, u16, i16),
    i14(14, u16, i16),
    i15(15, u16, i16),
    i17(17, u32, i32),
    i18(18, u32, i32),
    i19(19, u32, i32),
    i20(20, u32, i32),
    i21(21, u32, i32),
    i22(22, u32, i32),
    i23(23, u32, i32),
    i24(24, u32, i32),
    i25(25, u32, i32),
    i26(26, u32, i32),
    i27(27, u32, i32),
    i28(28, u32, i32),
    i29(29, u32, i32),
    i30(30, u32, i32),
    i31(31, u32, i32),
    i33(33, u64, i64),
    i34(34, u64, i64),
    i35(35, u64, i64),
    i36(36, u64, i64),
    i37(37, u64, i64),
    i38(38, u64, i64),
    i39(39, u64, i64),
    i40(40, u64, i64),
    i41(41, u64, i64),
    i42(42, u64, i64),
    i43(43, u64, i64),
    i44(44, u64, i64),
    i45(45, u64, i64),
    i46(46, u64, i64),
    i47(47, u64, i64),
    i48(48, u64, i64),
    i49(49, u64, i64),
    i50(50, u64, i64),
    i51(51, u64, i64),
    i52(52, u64, i64),
    i53(53, u64, i64),
    i54(54, u64, i64),
    i55(55, u64, i64),
    i56(56, u64, i64),
    i57(57, u64, i64),
    i58(58, u64, i64),
    i59(59, u64, i64),
    i60(60, u64, i64),
    i61(61, u64, i64),
    i62(62, u64, i64),
    i63(63, u64, i64)
);

new_unsigned_types!(
    u1(1, u8),
    u2(2, u8),
    u3(3, u8),
    u4(4, u8),
    u5(5, u8),
    u6(6, u8),
    u7(7, u8),
    u9(9, u16),
    u10(10, u16),
    u11(11, u16),
    u12(12, u16),
    u13(13, u16),
    u14(14, u16),
    u15(15, u16),
    u17(17, u32),
    u18(18, u32),
    u19(19, u32),
    u20(20, u32),
    u21(21, u32),
    u22(22, u32),
    u23(23, u32),
    u24(24, u32),
    u25(25, u32),
    u26(26, u32),
    u27(27, u32),
    u28(28, u32),
    u29(29, u32),
    u30(30, u32),
    u31(31, u32),
    u33(33, u64),
    u34(34, u64),
    u35(35, u64),
    u36(36, u64),
    u37(37, u64),
    u38(38, u64),
    u39(39, u64),
    u40(40, u64),
    u41(41, u64),
    u42(42, u64),
    u43(43, u64),
    u44(44, u64),
    u45(45, u64),
    u46(46, u64),
    u47(47, u64),
    u48(48, u64),
    u49(49, u64),
    u50(50, u64),
    u51(51, u64),
    u52(52, u64),
    u53(53, u64),
    u54(54, u64),
    u55(55, u64),
    u56(56, u64),
    u57(57, u64),
    u58(58, u64),
    u59(59, u64),
    u60(60, u64),
    u61(61, u64),
    u62(62, u64),
    u63(63, u64)
);

/// Implement functions for converting to/from byte arrays
///
/// Used for our numeric types that are an integer number of bytes.
macro_rules! byte_from_impls {
    ($($kind: ident: $super_kind: ty)*) => {
        $(
        impl $kind {
            /// The size of byte array equal to this value
            const ARR_SIZE: usize = <$kind>::COUNT / 8;
            /// The size of byte array equal to the underlying storage for this value
            const SUPER_BYTES: usize = core::mem::size_of::<$super_kind>();
            /// Convert from an array of bytes, in big-endian order
            pub fn from_be_bytes(bytes: [u8; Self::ARR_SIZE]) -> Self {
                let mut res_bytes = [0_u8; Self::SUPER_BYTES];
                for (set, &get) in res_bytes.iter_mut().rev().zip(bytes.iter().rev()) {
                    *set = get;
                }
                Self(<$super_kind>::from_be_bytes(res_bytes))
            }

            /// Convert `self` into an array of bytes, in big-endian order
            pub fn to_be_bytes(self) -> [u8; Self::ARR_SIZE] {
                let mut res = [0; Self::ARR_SIZE];
                let inner_bytes = self.0.to_be_bytes();
                for (&get, set) in inner_bytes.iter().rev().zip(res.iter_mut().rev()) {
                    *set = get;
                }
                res
            }

            /// Convert from an array of bytes, in little-endian order
            pub fn from_le_bytes(bytes: [u8; Self::ARR_SIZE]) -> Self {
                let mut res_bytes = [0_u8; Self::SUPER_BYTES];
                for (set, &get) in res_bytes.iter_mut().zip(bytes.iter()) {
                    *set = get;
                }
                Self(<$super_kind>::from_le_bytes(res_bytes))
            }

            /// Convert `self` into an array of bytes, in little-endian order
            pub fn to_le_bytes(self) -> [u8; Self::ARR_SIZE] {
                let mut res = [0; Self::ARR_SIZE];
                let inner_bytes = self.0.to_le_bytes();
                for (&get, set) in inner_bytes.iter().zip(res.iter_mut()) {
                    *set = get;
                }
                res
            }
        }

        impl From<u8> for $kind {
            fn from(byte: u8) -> Self {
                let inner = <$super_kind>::from(byte);
                $kind(inner)
            }
        }
        )*
    };
}

byte_from_impls! {
    u24: u32
    u40: u64
    u48: u64
    u56: u64
    i24: u32
    i40: u64
    i48: u64
    i56: u64
}

/// Implement `From` for new types easily
macro_rules! numeric_from_impls {
    ($(($newty:ty: $($basety:ty),+ $(,)?)),+ $(,)?) => {
        $(
        $(
        impl From<$basety> for $newty {
            fn from(n: $basety) -> Self {
                Self(n.into())
            }
        }
        )+
        )+
    };
}
numeric_from_impls!(
    (u24: u16),
    (u40: u16, u32),
    (u48: u16, u32),
    (u56: u16, u32),
    (i24: u16,),
    (i40: u16, u32),
    (i48: u16, u32),
    (i56: u16, u32),
);

impl<
        'a,
        P: Num + Bounded + ShlAssign<usize> + ShrAssign<usize> + BitCount,
        T,
        const START: usize,
        const STOP: usize,
    > GetSet<'a, P, T, START, STOP>
{
    /// Create a new [`GetSet`]. This should be called from methods generated by
    /// the [`bit_struct`] macro
    pub fn new(parent: &'a mut P) -> Self {
        Self {
            parent,
            _phantom: PhantomData::default(),
        }
    }

    /// Get a mask of `STOP-START + 1` length. This doesn't use the shift left
    /// and subtract one trick because of the special case where `(0b1 <<
    /// (STOP - START + 1)) - 1` will cause an overflow
    // Because `GetSet` has a lot of type parameters, it's easiest to be able to invoke this method
    // directly on a value instead of having to match the type parameters.
    #[allow(clippy::unused_self)]
    fn mask(&self) -> P {
        let num_bits = P::COUNT;
        let mut max_value = P::max_value();
        let keep_bits = STOP - START + 1;

        max_value >>= num_bits - keep_bits;
        max_value
    }
}

/// Check whether the underlying bits are valid
///
/// The type implementing this trait checks if the value stored in a bit
/// representation of type `P` is a valid representation of this type. The
/// [`enums`] macro implements this type for all of the integer-byte-width types
/// from this crate.
///
/// # Safety
///
/// The [`ValidCheck::is_valid`] function must be correctly implemented or else
/// other functions in this crate won't work correctly. Implementation of this
/// trait is preferably done by public macros in this crate, which will
/// implement it correctly.
pub unsafe trait ValidCheck<P> {
    /// Set this to true if, at compile-time, we can tell that all bit
    /// representations which contain the appropriate number of bits are valid
    /// representations of this type
    const ALWAYS_VALID: bool = false;
    /// Return whether or not the underlying bits of `P` are valid
    /// representation of this type
    fn is_valid(_input: P) -> bool {
        true
    }
}

impl<
        'a,
        P: Num
            + Shl<usize, Output = P>
            + Shr<usize, Output = P>
            + ShlAssign<usize>
            + ShrAssign<usize>
            + Bounded
            + BitAnd<Output = P>
            + Copy
            + BitCount,
        T: ValidCheck<P>,
        const START: usize,
        const STOP: usize,
    > GetSet<'a, P, T, START, STOP>
{
    /// Get the property this `GetSet` points at
    pub fn get(&self) -> T {
        let section = self.get_raw();
        // Safety:
        // This is guaranteed to be safe because the underlying storage must be bigger
        // than any fields stored within
        unsafe { core::mem::transmute_copy(&section) }
    }

    /// Returns true if the memory this `GetSet` points at is a valid
    /// representation of `T`
    pub fn is_valid(&self) -> bool {
        let section = self.get_raw();
        T::is_valid(section)
    }

    /// Get the raw bits being pointed at, without type conversion nor any form
    /// of validation
    pub fn get_raw(&self) -> P {
        let parent = *self.parent;
        let mask = self.mask();
        (parent >> START) & mask
    }
}

impl<'a, P, T, const START: usize, const STOP: usize> GetSet<'a, P, T, START, STOP>
where
    P: Num
        + Shl<usize, Output = P>
        + Copy
        + BitOrAssign
        + BitXorAssign
        + BitAnd<Output = P>
        + ShlAssign<usize>
        + ShrAssign<usize>
        + PartialOrd
        + Bounded
        + Sized
        + BitCount,
    T: FieldStorage,
    <T as FieldStorage>::StoredType: Into<P>,
{
    /// Set the property in the slice being pointed to by this `GetSet`
    pub fn set(&mut self, value: T) {
        // SAFETY:
        // This is safe because we produce it from a valid value of `T`, so we meet the
        // safety condition on `set_raw`
        unsafe { self.set_raw(value.inner_raw().into()) }
    }

    /// Set the field to a raw value.
    /// # Safety
    /// value must be a valid representation of the field. i.e.,
    /// `core::mem::transmute` between P and T must be defined.
    pub unsafe fn set_raw(&mut self, value: P) {
        let mask = self.mask();
        let mask_shifted = mask << START;

        // zero out parent
        *self.parent |= mask_shifted;
        *self.parent ^= mask_shifted;

        let to_set = value & mask;
        *self.parent |= to_set << START;
    }
}

/// A trait that all bit structs implement
///
/// See the [`bit_struct`] macro for more details.
pub trait BitStruct<const ALWAYS_VALID: bool> {
    /// The underlying type used to store the bit struct
    type Kind;
    /// Produce a bit struct from the given underlying storage, without checking
    /// for validity.
    ///
    /// # Safety
    ///
    /// The caller is responsible for verifying that this value is a valid value
    /// for the bit struct.
    ///
    /// If this is guaranteed to be safe (i.e. all possibly inputs for `value`
    /// are valid), then the bit struct will also implement [`BitStructExt`]
    /// which has the [`BitStructExt::exact_from`] method, that you should
    /// use instead.
    unsafe fn from_unchecked(value: Self::Kind) -> Self;
}

/// An extension trait for bit structs which can be safely made from any value
/// in their underlying storage type.
pub trait BitStructExt: BitStruct<true> {
    /// Produce a bit struct from the given underlying storage
    fn exact_from(value: Self::Kind) -> Self;
}

impl<T: BitStruct<true>> BitStructExt for T {
    fn exact_from(value: Self::Kind) -> Self {
        // SAFETY:
        // This is safe because this method only exists for bitfields for which it is
        // always safe to call `from_unchecked`
        unsafe { Self::from_unchecked(value) }
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! impl_fields {

    ($on: expr, $kind: ty =>
    [$($first_field_doc: expr),*], $head_field: ident, $head_actual: ty $(, [$($field_doc: expr),*], $field: ident, $actual: ty)*) => {
        $(#[doc=$first_field_doc])*
        pub fn $head_field(&mut self) -> $crate::GetSet<'_, $kind, $head_actual, {$on - <$head_actual as $crate::BitCount>::COUNT}, {$on - 1}> {
            $crate::GetSet::new(unsafe {self.0.as_ref_mut()})
        }

        $crate::impl_fields!($on - <$head_actual as $crate::BitCount>::COUNT, $kind => $([$($field_doc),*], $field, $actual),*);
    };
    ($on: expr, $kind: ty =>) => {};
}

/// Helper macro
#[doc(hidden)]
#[macro_export]
macro_rules! bit_struct_impl {
    (
        $(#[doc = $struct_doc:expr])*
        #[derive(Default)]
        $struct_vis: vis struct $name: ident ($kind: ty) {
        $(
            $(#[doc = $field_doc:expr])*
            $field: ident: $actual: ty
        ),* $(,)?
        }
    ) => {

        $crate::bit_struct_impl!(
        $(#[doc = $struct_doc])*
        $struct_vis struct $name ($kind) {
        $(
            $(#[doc = $field_doc])*
            $field: $actual
        ),*
        }

        );

        impl Default for $name {
            fn default() -> Self {
                Self::of_defaults()
            }
        }

    };

    (
        $(#[doc = $struct_doc:expr])*
        $struct_vis: vis struct $name: ident ($kind: ty) {
        $(
            $(#[doc = $field_doc:expr])*
            $field: ident: $actual: ty
        ),* $(,)?
        }
    ) => {

        impl $name {

            /// Creates an empty struct. This may or may not be valid
            pub unsafe fn empty() -> Self {
                unsafe { Self::from_unchecked(<$kind as $crate::BitStructZero>::bs_zero()) }
            }

            #[doc = concat!("Returns a valid representation for ", stringify!($name), "where all values are")]
            /// the defaults
            ///
            /// This is different than [`Self::default()`], because the actual default implementation
            /// might not be composed of only the defaults of the given fields.
            pub fn of_defaults() -> Self {
                let mut res = unsafe { Self::from_unchecked(<$kind as $crate::BitStructZero>::bs_zero()) };
                $(
                    res.$field().set(Default::default());
                )*
                res
            }
        }

        impl ::core::fmt::Debug for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> core::fmt::Result {
                let mut copied = *self;
                f.debug_struct(stringify!($name))
                    $(
                        .field(stringify!($field), &copied.$field().get())
                    )*
                    .finish()
            }
        }
    };
}

/// A bit struct which has a zero value we can get
pub trait BitStructZero: Zero {
    /// Get a zero value for this bit struct
    fn bs_zero() -> Self {
        Self::zero()
    }
}

impl<T: Zero> BitStructZero for T {}

// the main is actually needed

#[allow(clippy::needless_doctest_main)]
/// Create a bit struct.
///
///
/// This macro can only be used once for each module.
/// This is because the macro creates sub-module to limit access to certain
/// unsafe access. In the macro, bit-structs can be defined just like a struct
/// outside of the the macro. The catch is a **base type** must be specified.
/// Valid base types are u{8,16,32,64,128}. The elements stored in the struct
/// are statically guaranteed to not exceed the number of bits in the base type.
/// This means we cannot store a `u16` in a `u8`, but it also means we cannot
/// store 9 `u1`s in a u8.
///
/// Elements start at the top of the number (for a u16 this would be the 15th
/// bit) and progress down.
///
/// # Example
/// ```
/// bit_struct::enums! {
///     /// The default value for each enum is always the first
///     pub ThreeVariants { Zero, One, Two }
///
///     /// This is syntax to set the default value to Cat
///     pub Animal(Cat) { Cow, Bird, Cat, Dog }
///
///     pub Color { Orange, Red, Blue, Yellow, Green }
/// }
///
/// bit_struct::bit_struct! {
///     /// We can write documentation for the struct here. Here BitStruct1
///     /// derives default values from the above enums macro
///     #[derive(Default)]
///     struct BitStruct1 (u16){
///         /// a 1 bit element. This is stored in u16[15]
///         a: bit_struct::u1,
///
///         /// This is calculated to take up 2 bits. This is stored in u16[13..=14]
///         variant: ThreeVariants,
///
///         /// This also takes 2 bits. This is stored in u16[11..=12]
///         animal: Animal,
///
///         /// This takes up 3 bits. This is stored u16[8..=10]
///         color: Color,
///     }
///
///     struct BitStruct2(u32) {
///         /// We could implement for this too. Note, this does not have a default
///         a_color: Color,
///         b: bit_struct::u3,
///     }
/// }
///
/// fn main() {
///     use std::convert::TryFrom;
///     let mut bit_struct: BitStruct1 = BitStruct1::default();
///
///     assert_eq!(bit_struct.a().start(), 15);
///     assert_eq!(bit_struct.a().stop(), 15);
///
///     assert_eq!(bit_struct.color().start(), 8);
///     assert_eq!(bit_struct.color().stop(), 10);
///
///     assert_eq!(
///         format!("{:?}", bit_struct),
///         "BitStruct1 { a: 0, variant: Zero, animal: Cat, color: Orange }"
///     );
///     assert_eq!(bit_struct.raw(), 4096);
///
///     let reverse_bit_struct = BitStruct1::try_from(4096);
///     assert_eq!(
///         format!("{:?}", reverse_bit_struct),
///         "Ok(BitStruct1 { a: 0, variant: Zero, animal: Cat, color: Orange })"
///     );
///
///     // u3! macro provides a static assert that the number is not too large
///     let mut other_struct = BitStruct2::new(Color::Green, bit_struct::u3!(0b101));
///     assert_eq!(
///         format!("{:?}", other_struct),
///         "BitStruct2 { a_color: Green, b: 5 }"
///     );
///
///     assert_eq!(other_struct.a_color().get(), Color::Green);
///
///     other_struct.a_color().set(Color::Red);
///
///     assert_eq!(other_struct.a_color().get(), Color::Red);
/// }
/// ```
#[macro_export]
macro_rules! bit_struct {
    (
        $(
        $(#[doc = $struct_doc:expr])*
        $(#[derive($($struct_der: ident),+)])?
        $struct_vis: vis struct $name: ident ($kind: ty) {
        $(
            $(#[doc = $field_doc:expr])*
            $field: ident: $actual: ty
        ),* $(,)?
        }
        )*
    ) => {
        $(
        $(#[doc = $struct_doc])*
        #[derive(Copy, Clone, PartialOrd, PartialEq, Eq, Ord, Hash)]
        pub struct $name($crate::UnsafeStorage<$kind>);

        impl $crate::serde::Serialize for $name {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: $crate::serde::Serializer {

                let mut v = *self;
                #[derive($crate::serde::Serialize)]
                struct Raw {
                    $($field: $actual),*
                }

                let raw = Raw {
                    $($field: v.$field().get(),)*
                };

                raw.serialize(serializer)
            }
        }

        impl $crate::serde::Deserialize<'static> for $name {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error> where D: $crate::serde::Deserializer<'static> {

                #[derive($crate::serde::Deserialize)]
                struct Raw {
                    $($field: $actual),*
                }

                let raw = Raw::deserialize(deserializer)?;

                Ok($name::new(
                    $(raw.$field),*
                ))
            }
        }

        impl TryFrom<$kind> for $name {
            type Error = ();
            fn try_from(elem: $kind) -> Result<$name, ()> {
                let mut res = unsafe{Self::from_unchecked(elem)};
                $(
                    if !res.$field().is_valid() {
                        return Err(());
                    }
                )*
                Ok(res)
            }
        }

        impl $crate::BitStruct<{$(<$actual as $crate::ValidCheck<$kind>>::ALWAYS_VALID &&)* true}> for $name {
            type Kind = $kind;

            unsafe fn from_unchecked(inner: $kind) -> Self {
               Self(unsafe {$crate::UnsafeStorage::new_unsafe(inner)})
            }
        }

        impl $name {

            unsafe fn from_unchecked(inner: $kind) -> Self {
               Self(unsafe {$crate::UnsafeStorage::new_unsafe(inner)})
            }

            #[allow(clippy::too_many_arguments)]
            pub fn new($($field: $actual),*) -> Self {
                let mut res = unsafe { Self::from_unchecked(<$kind as $crate::BitStructZero>::bs_zero()) };
                $(
                    res.$field().set($field);
                )*
                res
            }

            pub fn raw(self) -> $kind {
                self.0.inner()
            }

            $crate::impl_fields!(<$kind as $crate::BitCount>::COUNT, $kind => $([$($field_doc),*], $field, $actual),*);
        }

        )*

        $(
        $crate::bit_struct_impl!(
        $(#[doc = $struct_doc])*
        $(#[derive($($struct_der),+)])?
        $struct_vis struct $name ($kind) {
        $(
            $(#[doc = $field_doc])*
            $field: $actual
        ),*
        }

        );
        )*
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! count_idents {
    ($on: expr, [$head: ident $(,$xs: ident)*]) => {
        $crate::count_idents!($on + 1, [$($xs),*])
    };
    ($on: expr, []) => {
        $on
    }
}

/// Returns the index of the leading 1 in `num`
///
/// Example:
/// ```
/// # use bit_struct::bits;
///
/// assert_eq!(bits(2), 2);
/// assert_eq!(bits(3), 2);
/// assert_eq!(bits(5), 3);
/// assert_eq!(bits(32), 6);
/// ```
pub const fn bits(num: usize) -> usize {
    /// Helper function for [`bits`]
    const fn helper(count: usize, on: usize) -> usize {
        // 0b11 = 3  log2_ceil(0b11) = 2 .. 2^2
        // 0b10 = 2 log2_ceil = 2 .. 2^1
        if on > 0 {
            helper(count + 1, on >> 1)
        } else {
            count
        }
    }

    helper(0, num)
}

/// Helper macro
#[doc(hidden)]
#[macro_export]
macro_rules! enum_impl {
    (FROMS $name: ident: [$($kind: ty),*]) => {
        $(
        impl From<$name> for $kind {
            fn from(value: $name) -> Self {
                Self::from(value as u8)
            }
        }
        )*
    };
    (VALID_CORE $name: ident: [$($kind: ty),*]) => {
        $(
        unsafe impl $crate::ValidCheck<$kind> for $name {
            const ALWAYS_VALID: bool = <Self as $crate::ValidCheck<u8>>::ALWAYS_VALID;
            fn is_valid(value: $kind) -> bool {
                Self::is_valid(value as u8)
            }
        }
        )*
    };
    (COUNT $head:ident $(,$xs: ident)*) => {
       1 + $crate::enum_impl!(COUNT $($xs),*)
    };
    (COUNT) => {
        0
    };
    (VALID_BIT_STRUCT $name: ident: [$($kind: ty),*]) => {
        $(
        unsafe impl $crate::ValidCheck<$kind> for $name {
            const ALWAYS_VALID: bool = <Self as $crate::ValidCheck<u8>>::ALWAYS_VALID;
            fn is_valid(value: $kind) -> bool {
                let inner = value.value();
                Self::is_valid(inner as u8)
            }
        }
        )*
    };
    (FROM_IMPLS $name: ident) => {
        $crate::enum_impl!(VALID_CORE $name: [u16, u32, u64, u128]);
        $crate::enum_impl!(VALID_BIT_STRUCT $name: [$crate::u24, $crate::u40, $crate::u48, $crate::u56]);
        $crate::enum_impl!(FROMS $name: [u8, u16, u32, u64, u128, $crate::u24, $crate::u40, $crate::u48, $crate::u56]);

        impl $crate::FieldStorage for $name {
            type StoredType = u8;

            fn inner_raw(self) -> Self::StoredType {
                self as Self::StoredType
            }
        }

    };
    (
        $(#[doc = $struct_doc:expr])*
        $(#[derive($($struct_der:ident),+)])?
        $enum_vis: vis $name: ident($default: ident){
            $(#[doc = $fst_field_doc:expr])*
            $fst_field: ident
            $(,
                $(#[doc = $field_doc:expr])*
                $field: ident
            )* $(,)?
        }
    ) => {

        #[repr(u8)]
        $(#[doc = $struct_doc])*
        $(#[derive($($struct_der),+)])?
        #[derive(Copy, Clone, Debug, PartialOrd, PartialEq, Eq, $crate::serde::Serialize, $crate::serde::Deserialize)]
        $enum_vis enum $name {
            $(#[doc = $fst_field_doc])*
            $fst_field,
            $(
                $(#[doc = $field_doc])*
                $field
            ),*
        }

        unsafe impl $crate::BitCount for $name {
            const COUNT: usize = $crate::bits($crate::count_idents!(0, [$($field),*]));
        }

        impl $name {
            const VARIANT_COUNT: usize = $crate::enum_impl!(COUNT $fst_field $(,$field)*);
        }

        unsafe impl $crate::ValidCheck<u8> for $name {
            const ALWAYS_VALID: bool = Self::VARIANT_COUNT.count_ones() == 1;
            fn is_valid(value: u8) -> bool {
                if (value as usize) < Self::VARIANT_COUNT {
                    true
                } else {
                    false
                }
            }
        }

        $crate::enum_impl!(FROM_IMPLS $name);

        impl Default for $name {
            fn default() -> Self {
                Self::$default
            }
        }

    };


    (
        $(#[doc = $struct_doc:expr])*
        $(#[derive($($struct_der:ident),+)])?
        $enum_vis: vis $name: ident {
            $(#[doc = $fst_field_doc:expr])*
            $fst_field: ident
            $(,
                $(#[doc = $field_doc:expr])*
                $field: ident
            )* $(,)?
        }
    ) => {
        #[repr(u8)]
        $(#[doc = $struct_doc])*
        $(#[derive($($struct_der),+)])?
        #[derive(Copy, Clone, Debug, PartialOrd, PartialEq, Eq, $crate::serde::Serialize, $crate::serde::Deserialize)]
        $enum_vis enum $name {
            $(#[doc = $fst_field_doc])*
            $fst_field,
            $(
                $(#[doc = $field_doc])*
                $field
            ),*
        }

        impl Default for $name {
            fn default() -> Self {
                Self::$fst_field
            }
        }

        impl $name {
            const VARIANT_COUNT: usize = $crate::enum_impl!(COUNT $fst_field $(,$field)*);
        }

        unsafe impl $crate::BitCount for $name {
            const COUNT: usize = $crate::bits($crate::count_idents!(0, [$($field),*]));
        }


        unsafe impl $crate::ValidCheck<u8> for $name {
            const ALWAYS_VALID: bool = Self::VARIANT_COUNT.count_ones() == 1;

            fn is_valid(value: u8) -> bool {
                if (value as usize) < Self::VARIANT_COUNT {
                    true
                } else {
                    false
                }
            }
        }

        $crate::enum_impl!(FROM_IMPLS $name);
    };
}

/// Create enums with trait implementations necessary for use in a `bit_struct`
/// field.
///
/// Example:
/// ```
/// # use bit_struct::enums;
///
/// enums! {
///     pub Colors { Red, Green, Blue }
///
///     Shapes { Triangle, Circle, Square }
/// }
/// ```
///
/// By default, this macro produces an impl of [`Default`] in which the first
/// field listed is made the default. However, you can also specify some other
/// variant as the default, as follows:
/// ```
/// # use bit_struct::enums;
///
/// enums! {
///     DefaultsToA { A, B, C }
///     DefaultsToB (B) { A, B, C }
/// }
///
/// assert_eq!(DefaultsToA::default(), DefaultsToA::A);
/// assert_eq!(DefaultsToB::default(), DefaultsToB::B);
/// ```
#[macro_export]
macro_rules! enums {
    (
        $(
        $(#[doc = $struct_doc:expr])*
        $(#[derive($($struct_der:ident),+)])?
        $enum_vis: vis $name: ident $(($enum_default: ident))? {
            $(#[doc = $fst_field_doc:expr])*
            $fst_field: ident
            $(,
                $(#[doc = $field_doc:expr])*
                $field: ident
            )* $(,)?
        }
        )+
    ) => {
        $(
        $crate::enum_impl!(
        $(#[doc = $struct_doc])*
        $(#[derive($($struct_der),+)])?
        $enum_vis $name $(($enum_default))?{
            $(#[doc = $fst_field_doc])*
            $fst_field
            $(,
                $(#[doc = $field_doc])*
                $field
            )*
        }
        );
        )+
    }
}

/// Create a `bit_struct`
#[macro_export]
macro_rules! create {
    (
        $struct_kind: ty {
            $($field: ident: $value: expr),* $(,)?
        }
    ) => {
        {
            let mut res = <$struct_kind>::of_defaults();
            $(
                res.$field().set($value);
            )*
            res
        }
    };
}
