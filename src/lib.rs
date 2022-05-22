use core::fmt;
use core::fmt::{Debug, Display};
use core::hash::Hash;
use core::marker::PhantomData;
use core::ops::{BitAnd, BitOr};

pub mod list;

/// Implementation of bitset. See [`Value`]
#[derive(Copy, Clone, Default, Eq, PartialEq, Debug, Hash)]
pub struct Cons<B, S>(PhantomData<(B, S)>);

impl<B: Display + Default, S: Display + Default> Display for Cons<B, S> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
		write!(
			f,
			"{}{}",
			<S as Default>::default(),
			<B as Default>::default()
		)
	}
}

/// Represents a bitset represented as zero.
/// Only if a bitset equals to [`Bit0`], the bitset means zero.
/// See [`Value`] for details.
#[derive(Copy, Clone, Default, Eq, PartialEq, Debug, Hash)]
pub struct Bit0;
impl Display for Bit0 {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "0")
	}
}

/// Represents a bitset represented as one.
/// See [`Value`] for details.
#[derive(Copy, Clone, Default, Eq, PartialEq, Debug, Hash)]
pub struct Bit1;
impl Display for Bit1 {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "1")
	}
}

/// The main trait represents a bitset.
///
/// [`Value`] is an representation of non-negative number. It can be converted
/// to `usize` number via [`Value::as_usize`] or [`Value::N`].
///
/// [`Value`] is one of [`Bit`], [`Cons<B, S>`] where `B: Bit, S: Positive`.
/// Because the constraint of `S: Positive`, the type representation of a number
/// is uniquely decided. Thus the following code is not allowed:
///
/// ```compile_fail
/// # use typebitset::{Value, Cons, Bit0, Bit1};
/// fn check<T: Value>() -> usize { T::N  }
/// check::<Cons<Bit0, Bit0>>();
/// ```
/// ```compile_fail
/// # use typebitset::{Value, Cons, Bit0, Bit1};
/// # fn check<T: Value>() -> usize { T::N  }
/// check::<Cons<Bit0, Cons<Bit0, Bit0>>>();
/// ```
///
/// And the followings are consistent.
///
/// ```
/// # use typebitset::{Value, Cons, Bit0, Bit1};
/// # fn check<T: Value>() -> usize { T::N  }
/// assert_eq!(
/// 	check::<Cons<Bit1, Cons<Bit0, Bit1>>>(),
/// 	0b101
/// );
/// ```
///
/// You can use [`FromNum<N>`] to create [`Value`] type for small number `N`.
/// See [`FromNum`] for details.
///
/// Operators [`BitAnd`] and [`BitOr`] are supported.
///
/// ```
/// # use typebitset::{FromNum, Bit0, Bit1};
/// let _: FromNum<0b101> = <FromNum<0b100> as Default>::default() | Bit1;
/// let _: FromNum<0b1> = <FromNum<0b111> as Default>::default() & Bit1;
/// ```
pub trait Value: Copy + Clone + Default + Eq + PartialEq + Debug + Hash {
	/// Integer representation of the bitset.
	const N: usize;

	/// Convert the [`Value`] val to `usize`.
	fn as_usize(&self) -> usize {
		Self::N
	}
}

impl Value for Bit0 {
	const N: usize = 0;
}

impl Value for Bit1 {
	const N: usize = 1;
}

impl<B: Bit, S: Positive> Value for Cons<B, S> {
	const N: usize = <S as Value>::N * 2 + <B as Value>::N;
}

macro_rules! value_from {
	([$($par:ident: $type:ident),*] $obj:ident) => {
		impl<$($par : $type),*> From<$obj<$($par),*>> for usize
		{
			fn from(_: $obj<$($par),*>) -> usize {
				<$obj<$($par),*>>::N
			}
		}

		impl<$($par : $type),*> $obj<$($par),*>
		{
			const N: usize = <Self as Value>::N;
			pub fn as_usize(&self) -> usize {
				Self::N
			}
		}
	};
}

value_from!([] Bit0);
value_from!([] Bit1);
value_from!([B: Bit, S: Positive] Cons);

/// A trait implemented if the bitset is positive (not zero).
///
/// ```
/// # use typebitset::{FromNum, Positive};
/// fn test<T: Positive>() {}
/// test::<FromNum<1>>();
/// test::<FromNum<2>>();
/// test::<FromNum<3>>();
/// ```
/// ```compile_fail
/// # use typebitset::{FromNum, Positive};
/// # fn test<T: Positive>() {}
/// // fail
/// test::<FromNum<0>>();
/// ```
pub trait Positive: Value {}
impl Positive for Bit1 {}
impl<B: Bit, S: Positive> Positive for Cons<B, S> {}

/// A trait which represents a bit.
pub trait Bit: Value {}
impl Bit for Bit0 {}
impl Bit for Bit1 {}

/// Generate left shift of the bitset.
///
/// ```
/// # use typebitset::{FromNum, ShiftRaising};
/// let a: FromNum<0b1010> = <
/// 	<
/// 		FromNum<0b101> as ShiftRaising
/// 	>::Output as Default
/// >::default();
/// assert_eq!(a.as_usize(), 0b1010);
/// ```
pub trait ShiftRaising {
	type Output: Value;
	fn shift_raising(self) -> Self::Output;
}

impl ShiftRaising for Bit0 {
	type Output = Bit0;
	fn shift_raising(self) -> Self::Output {
		Bit0
	}
}

impl ShiftRaising for Bit1 {
	type Output = Cons<Bit0, Bit1>;
	fn shift_raising(self) -> Self::Output {
		Cons(PhantomData)
	}
}

impl<B, S> ShiftRaising for Cons<B, S>
where
	S: Positive,
	B: Bit,
{
	type Output = Cons<Bit0, Cons<B, S>>;
	fn shift_raising(self) -> Self::Output {
		Cons(PhantomData)
	}
}

/// Generate right shift of the bitset.
///
/// ```
/// # use typebitset::{FromNum, ShiftLowering};
/// let a: FromNum<0b101> = <
/// 	<
/// 		FromNum<0b1010> as ShiftLowering
/// 	>::Output as Default
/// >::default();
/// assert_eq!(a.as_usize(), 0b101);
/// ```
pub trait ShiftLowering {
	type Output: Value;
	/// The LSB, dropped from `Self`.
	///
	/// ```
	/// # use typebitset::{Bit0,Bit1,FromNum, ShiftLowering};
	/// let _: Bit0 = <<
	/// 	FromNum<0b1010> as ShiftLowering
	/// >::Lsb as Default>::default();
	/// let _: Bit1 = <<
	/// 	FromNum<0b101> as ShiftLowering
	/// >::Lsb as Default>::default();
	/// ```
	type Lsb: Bit;
	fn shift_lowering(self) -> Self::Output;
}

impl ShiftLowering for Bit0 {
	type Output = Bit0;
	type Lsb = Bit0;
	fn shift_lowering(self) -> Self::Output {
		Bit0
	}
}

impl ShiftLowering for Bit1 {
	type Output = Bit0;
	type Lsb = Bit1;
	fn shift_lowering(self) -> Self::Output {
		Bit0
	}
}

impl<B, S> ShiftLowering for Cons<B, S>
where
	S: Positive,
	B: Bit,
{
	type Output = S;
	type Lsb = B;
	fn shift_lowering(self) -> Self::Output {
		<S as Default>::default()
	}
}

/// Make left shift of the bitset and use give bit as the LSB.
///
/// ```
/// # use typebitset::{FromNum, ShiftRaising};
/// let a: FromNum<0b1010> = <
/// 	<
/// 		FromNum<0b101> as ShiftRaising
/// 	>::Output as Default
/// >::default();
/// assert_eq!(a.as_usize(), 0b1010);
/// ```
pub trait Push<B> {
	type Output: Value;
}

impl<B: Bit> Push<B> for Bit0 {
	type Output = B;
}

impl<B: Bit> Push<B> for Bit1 {
	type Output = Cons<B, Bit1>;
}

impl<B0: Bit, B: Bit, S: Positive> Push<B0> for Cons<B, S> {
	type Output = Cons<B0, Cons<B, S>>;
}

/// Replacing Bit1 in Self with S.
/// S should be [`Positive`].
///
/// ```
/// # use typebitset::{FromNum, ReplaceOnes};
/// let a: FromNum<0b1101100> = <
/// 	<
/// 		FromNum<0b10100> as ReplaceOnes<FromNum<0b11>>
/// 	>::Output as Default
/// >::default();
/// let b: FromNum<0b11100> = <
/// 	<
/// 		FromNum<0b100> as ReplaceOnes<FromNum<0b111>>
/// 	>::Output as Default
/// >::default();
/// assert_eq!(a.as_usize(), 0b1101100);
/// assert_eq!(b.as_usize(), 0b11100);
/// ```
pub trait ReplaceOnes<S> {
	type Output: Value;
}

impl<S> ReplaceOnes<S> for Bit0 {
	type Output = Bit0;
}

impl<S: Value> ReplaceOnes<S> for Bit1 {
	type Output = S;
}

impl<S, S0: ReplaceOnes<S>> ReplaceOnes<S> for Cons<Bit0, S0>
where
	<S0 as ReplaceOnes<S>>::Output: Positive,
{
	type Output = Cons<Bit0, <S0 as ReplaceOnes<S>>::Output>;
}

impl<S: PushAfterMsb<<S0 as ReplaceOnes<S>>::Output>, S0: ReplaceOnes<S>> ReplaceOnes<S>
	for Cons<Bit1, S0>
{
	type Output = <S as PushAfterMsb<<S0 as ReplaceOnes<S>>::Output>>::Output;
}

/// Concat bitset S after the MSB of Self.
///
/// ```
/// # use typebitset::{FromNum, PushAfterMsb};
/// let a: FromNum<0b1101> = <
/// 	<
/// 		FromNum<0b0> as PushAfterMsb<FromNum<0b1101>>
/// 	>::Output as Default
/// >::default();
/// let b: FromNum<0b1101100> = <
/// 	<
/// 		FromNum<0b100> as PushAfterMsb<FromNum<0b1101>>
/// 	>::Output as Default
/// >::default();
/// assert_eq!(<FromNum<0b1101> as Default>::default().as_usize(), 0b1101);
/// assert_eq!(a.as_usize(), 0b1101);
/// assert_eq!(b.as_usize(), 0b1101100);
/// ```
pub trait PushAfterMsb<S> {
	type Output: Value;
}

impl<S: Value> PushAfterMsb<S> for Bit0 {
	type Output = S;
}

impl<S: Positive> PushAfterMsb<S> for Bit1 {
	type Output = Cons<Bit1, S>;
}

impl<B: Bit, S: Positive, S0: PushAfterMsb<S>> PushAfterMsb<S> for Cons<B, S0>
where
	<S0 as PushAfterMsb<S>>::Output: Positive,
{
	type Output = Cons<B, <S0 as PushAfterMsb<S>>::Output>;
}

macro_rules! impl_binary_op {
	($($bita:ident, $bitb:ident, $bito_and:ident, $bito_or:ident;)*) => {
		$(
			impl BitAnd<$bita> for $bitb {
				type Output = $bito_and;
				fn bitand(self, _: $bita) -> Self::Output {
					$bito_and
				}
			}

			impl BitOr<$bita> for $bitb {
				type Output = $bito_or;
				fn bitor(self, _: $bita) -> Self::Output {
					$bito_or
				}
			}

			impl<Sa> BitAnd<Cons<$bita, Sa>> for $bitb
			where
				Cons<$bita, Sa>: Value
			{
				type Output = $bito_and;
				fn bitand(self, _: Cons<$bita, Sa>) -> Self::Output {
					$bito_and
				}
			}

			impl<Sb> BitAnd<$bita> for Cons<$bitb, Sb>
			where
				Cons<$bitb, Sb>: Value
			{
				type Output = $bito_and;
				fn bitand(self, _: $bita) -> Self::Output {
					$bito_and
				}
			}

			impl<Sa> BitOr<Cons<$bita, Sa>> for $bitb
			where
				Cons<$bita, Sa>: Value,
				Sa: Push<$bito_or>,
			{
				type Output = <Sa as Push<$bito_or>>::Output;
				fn bitor(self, _: Cons<$bita, Sa>) -> Self::Output {
					<Self::Output as Default>::default()
				}
			}

			impl<Sb> BitOr<$bita> for Cons<$bitb, Sb>
			where
				Cons<$bitb, Sb>: Value,
				Sb: Push<$bito_or>,
			{
				type Output = <Sb as Push<$bito_or>>::Output;
				fn bitor(self, _: $bita) -> Self::Output {
					<Self::Output as Default>::default()
				}
			}

			impl<Sa, Sb> BitAnd<Cons<$bita, Sa>> for Cons<$bitb, Sb>
			where
				Cons<$bita, Sa>: Value,
				Cons<$bitb, Sb>: Value,
				Sb: BitAnd<Sa>,
				<Sb as BitAnd<Sa>>::Output: Push<$bito_and>,
			{
				type Output = <<Sb as BitAnd<Sa>>::Output as Push<$bito_and>>::Output;
				fn bitand(self, _rhs: Cons<$bita, Sa>) -> Self::Output {
					<Self::Output as Default>::default()
				}
			}

			impl<Sa, Sb> BitOr<Cons<$bita, Sa>> for Cons<$bitb, Sb>
			where
				Cons<$bita, Sa>: Value,
				Cons<$bitb, Sb>: Value,
				Sb: BitOr<Sa>,
				<Sb as BitOr<Sa>>::Output: Push<$bito_or>,
			{
				type Output = <<Sb as BitOr<Sa>>::Output as Push<$bito_or>>::Output;
				fn bitor(self, _rhs: Cons<$bita, Sa>) -> Self::Output {
					<Self::Output as Default>::default()
				}
			}
		)*
	}
}

impl_binary_op! {
	// Lhs, Rhs, And, Or
	Bit0, Bit0, Bit0, Bit0;
	Bit1, Bit0, Bit0, Bit1;
	Bit0, Bit1, Bit0, Bit1;
	Bit1, Bit1, Bit1, Bit1;
}

#[doc(hidden)]
pub trait FromNumImpl<const N: usize> {
	type Output: Value;
}

/// Generate [`Value`] type for small number `N`.
/// [`FromNum<N>`] is defined where `N` is in `0..2 ** 7`.
///
/// For example, `FromNum<2>` is expanded to `Cons<Bit0, Bit1>`.
///
/// ```
/// # use typebitset::{Bit0, Bit1, Cons,FromNum};
/// let _: FromNum<0> = Bit0; // for minimum N
/// let _: FromNum<1> = Bit1;
/// let _: FromNum<2> = <Cons<Bit0, Bit1> as Default>::default();
/// let _: FromNum<3> = <Cons<Bit1, Bit1> as Default>::default();
/// let _: FromNum<4> = <Cons<Bit0, Cons<Bit0, Bit1>> as Default>::default();
/// let _: FromNum<{2_usize.pow(7) - 1}>; // for maximum N
/// ```
/// ```compile_fail
/// # use typebitset::FromNum;
/// let _: FromNum<{2_usize.pow(7)}>; // Compile error
/// ```
///
/// To create larger number, you can use [`ShiftRaising`] or [`Push`].
pub type FromNum<const N: usize> = <Bit0 as FromNumImpl<N>>::Output;

macro_rules! impl_set_of {
	(@out ) => { $crate::Bit0 };
	(@out 1) => { $crate::Bit1 };
	(@out 0 $(,$xs:tt)+) => {
		$crate::Cons<$crate::Bit0, impl_set_of!(@out $($xs),+)>
	};
	(@out 1 $(,$xs:tt)+) => {
		$crate::Cons<$crate::Bit1, impl_set_of!(@out $($xs),+)>
	};
	(@imp $($xs:tt),*) => {
		impl FromNumImpl<{impl_set_of!(@bittonum $($xs),*)}> for Bit0 {
			type Output = impl_set_of!(@out $($xs),*);
		}
	};
	(@bittonum ) => {0usize};
	(@bittonum $x0:tt $(,$xs:tt)*) => {
		2usize * (impl_set_of!(@bittonum $($xs),*)) + $x0
	};
	(@i [$($ys:tt),*] ) => {
		impl_set_of!(@imp $($ys),*);
	};
	(@i [$($ys:tt),*] 1) => {
		impl_set_of!(@i [$($ys,)* 1] );
	};
	(@i [$($ys:tt),*] 1 $(,$xs:tt)+) => {
		impl_set_of!(@i [$($ys,)* 1] $($xs),+);
		impl_set_of!(@i [$($ys,)* 0] $($xs),+);
	};
	() => {
		impl_set_of!(@imp );
	};
	(1 $(,$xs:tt)*) => {
		impl_set_of!(@i [] 1 $(,$xs)*);
		impl_set_of!($($xs),*);
	}
}

impl_set_of!(1, 1, 1, 1, 1, 1, 1);

#[cfg(test)]
mod test {
	use super::*;

	macro_rules! test_with_number {
		(@run $n:expr) => {
			let _: FromNum<{ $n * 2 }> = <<FromNum<{ $n }> as ShiftRaising>::Output>::default();
			let _: FromNum<{ $n * 4 }> =
				<<<FromNum<{ $n }> as ShiftRaising>::Output as ShiftRaising>::Output>::default();
			let _: FromNum<{ $n }> = <<FromNum<{ $n * 2 }> as ShiftLowering>::Output>::default();
			let _: FromNum<{ $n }> =
				<<<FromNum<{ $n * 4 }> as ShiftLowering>::Output as ShiftLowering>::Output>::default();
			let _: [(); <FromNum<{$n}>>::N - $n] = [];
		};
		(@ [$($ys:expr),*]) => {
			test_with_number!(@run 0usize $(+$ys)*);
		};
		(@ [$($ys:expr),*] $x:expr $(,$xs:expr)*) => {
			test_with_number!(@[$($ys),*]$($xs),*);
			test_with_number!(@[$($ys,)*$x]$($xs),*);
		};
		($($xs:expr),*) => {
			test_with_number!(@ [] $($xs),*);
		};
	}

	macro_rules! test_and_or {
		(@run $a: expr, $b: expr) => {
			let _: FromNum<{ $a & $b }> =
				<<FromNum<{ $a }> as BitAnd<FromNum<{$b}>>>::Output as Default>::default();
			let _: FromNum<{ $a | $b }> =
				<<FromNum<{ $a }> as BitOr<FromNum<{$b}>>>::Output as Default>::default();
		};
		(@ [$($ys: expr),*] [$($zs: expr),*]) => {
			test_and_or!(@run 0usize $(+ $ys)*, 0usize $(+ $zs)*);
		};
		(@ [$($ys: expr),*] [$($zs: expr),*] $x: expr $(,$xs: expr)*) => {
			test_and_or!(@ [$($ys),*] [$($zs),*] $($xs),*);
			test_and_or!(@ [$x $(,$ys)*] [$($zs),*] $($xs),*);
			test_and_or!(@ [$($ys),*] [$x $(,$zs)*] $($xs),*);
			test_and_or!(@ [$x $(,$ys)*] [$x $(,$zs)*] $($xs),*);
		};
		($($xs:expr),*) => {
			test_and_or!(@ [] [] $($xs),*);
		};
	}

	macro_rules! if_impl_trait {
		($t:ty : $tr:path) => {{
			trait DoesNotImpl {
				const IMPLS: bool = false;
			}
			impl<T> DoesNotImpl for T {}
			struct Wrapper<T>(PhantomData<T>);
			#[allow(dead_code)]
			impl<T> Wrapper<T>
			where
				T: $tr,
			{
				const IMPLS: bool = true;
			}
			<Wrapper<$t>>::IMPLS
		}};
	}

	#[test]
	fn test() {
		let v1: Cons<Bit1, Cons<Bit0, Bit1>> = Default::default();
		let v2: Cons<Bit1, Bit1> = Default::default();
		let _: Bit1 = v1 & v2;
		let _: Cons<Bit1, Cons<Bit1, Bit1>> = v1 | v2;
		let _v4: <<Bit0 as ShiftRaising>::Output as Push<Bit1>>::Output = Default::default();
		let _: (FromNum<6>, FromNum<12>) = <<(FromNum<6>, FromNum<8>) as list::BitOrAll<
			FromNum<4>,
		>>::Output as Default>::default();
		test_with_number!(1, 2, 4, 8, 16);
		test_and_or!(1, 2, 4, 8, 16);

		assert!(if_impl_trait!((FromNum<3>, FromNum<3>): list::SameList));
		assert!(!if_impl_trait!((FromNum<4>, FromNum<3>): list::SameList));
		assert!(if_impl_trait!((FromNum<3>, FromNum<1>): list::PositiveAll));
		assert!(!if_impl_trait!((FromNum<0>, FromNum<1>): list::PositiveAll));
	}
}
