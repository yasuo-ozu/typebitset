use core::fmt;
use core::fmt::{Debug, Display};
use core::hash::Hash;
use core::marker::PhantomData;
use core::ops::{BitAnd, BitOr};

/// Implementation of bitset. See [`Set`]
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
/// See [`Set`] for details.
#[derive(Copy, Clone, Default, Eq, PartialEq, Debug, Hash)]
pub struct Bit0;
impl Display for Bit0 {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "0")
	}
}

/// Represents a bitset represented as one.
/// See [`Set`] for details.
#[derive(Copy, Clone, Default, Eq, PartialEq, Debug, Hash)]
pub struct Bit1;
impl Display for Bit1 {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "1")
	}
}

/// The main trait represents a bitset.
pub trait Set: Copy + Clone + Default + Eq + PartialEq + Debug + Hash {
	/// Integer representation of the bitset.
	const N: usize;
}

impl Set for Bit0 {
	const N: usize = 0;
}

impl Set for Bit1 {
	const N: usize = 1;
}

impl<B: Bit, S: Positive> Set for Cons<B, S> {
	const N: usize = <S as Set>::N * 2 + 1;
}

/// A trait implemented if the bitset is positive (not zero).
pub trait Positive: Set {}
impl Positive for Bit1 {}
impl<B: Bit, S: Positive> Positive for Cons<B, S> {}

/// A trait which represents a bit.
pub trait Bit: Set {}
impl Bit for Bit0 {}
impl Bit for Bit1 {}

/// Generate left shift of the bitset.
pub trait ShiftRaising {
	type Output: Set;
}

impl ShiftRaising for Bit0 {
	type Output = Bit0;
}

impl ShiftRaising for Bit1 {
	type Output = Cons<Bit0, Bit1>;
}

impl<B, S> ShiftRaising for Cons<B, S>
where
	S: Positive,
	B: Bit,
{
	type Output = Cons<Bit0, Cons<B, S>>;
}

/// Generate right shift of the bitset.
pub trait ShiftLowering {
	type Output: Set;
}

impl ShiftLowering for Bit0 {
	type Output = Bit0;
}

impl ShiftLowering for Bit1 {
	type Output = Bit0;
}

impl<B, S> ShiftLowering for Cons<B, S>
where
	S: Positive,
	B: Bit,
{
	type Output = S;
}

/// Make left shift of the bitset and use give bit as the LSB.
pub trait Push<B> {
	type Output: Set;
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
				Cons<$bita, Sa>: Set
			{
				type Output = $bito_and;
				fn bitand(self, _: Cons<$bita, Sa>) -> Self::Output {
					$bito_and
				}
			}

			impl<Sb> BitAnd<$bita> for Cons<$bitb, Sb>
			where
				Cons<$bitb, Sb>: Set
			{
				type Output = $bito_and;
				fn bitand(self, _: $bita) -> Self::Output {
					$bito_and
				}
			}

			impl<Sa> BitOr<Cons<$bita, Sa>> for $bitb
			where
				Cons<$bita, Sa>: Set,
				Sa: Push<$bito_or>,
			{
				type Output = <Sa as Push<$bito_or>>::Output;
				fn bitor(self, _: Cons<$bita, Sa>) -> Self::Output {
					<Self::Output as Default>::default()
				}
			}

			impl<Sb> BitOr<$bita> for Cons<$bitb, Sb>
			where
				Cons<$bitb, Sb>: Set,
				Sb: Push<$bito_or>,
			{
				type Output = <Sb as Push<$bito_or>>::Output;
				fn bitor(self, _: $bita) -> Self::Output {
					<Self::Output as Default>::default()
				}
			}

			impl<Sa, Sb> BitAnd<Cons<$bita, Sa>> for Cons<$bitb, Sb>
			where
				Cons<$bita, Sa>: Set,
				Cons<$bitb, Sb>: Set,
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
				Cons<$bita, Sa>: Set,
				Cons<$bitb, Sb>: Set,
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

#[cfg(test)]
mod test {
	use super::*;

	trait FromNumImpl<const N: usize> {
		type Output;
	}

	type FromNum<const N: usize> = <Bit0 as FromNumImpl<N>>::Output;

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

	macro_rules! test_with_number {
		($n:expr) => {
			let _: FromNum<{ $n * 2 }> = <<FromNum<{ $n }> as ShiftRaising>::Output>::default();
			let _: FromNum<{ $n * 4 }> =
				<<<FromNum<{ $n }> as ShiftRaising>::Output as ShiftRaising>::Output>::default();
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

	#[test]
	fn test() {
		let v1: Cons<Bit1, Cons<Bit0, Bit1>> = Default::default();
		let v2: Cons<Bit1, Bit1> = Default::default();
		let _: Bit1 = v1 & v2;
		let _: Cons<Bit1, Cons<Bit1, Bit1>> = v1 | v2;
		let _v4: <<Bit0 as ShiftRaising>::Output as Push<Bit1>>::Output = Default::default();
		test_with_number!(10);
		test_and_or!(1, 2, 4, 8, 16);
	}
}
