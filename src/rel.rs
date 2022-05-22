use crate::{Bit, Bit0, Bit1, Cons, Positive, Value};

/// Represents that two [`Value`] are equal. Alternative of
/// [`std::cmp::PartialEq`].
///
/// As differerent from [`std::cmp::Eq`], [`Equal`] is only implemented on two
/// [`Value`]s that are equal.
///
/// ```
/// # use typebitset::rel::Equal;
/// # use typebitset::{Bit0,Bit1,FromNum};
/// fn check<T, U: Equal<T>>(){}
/// check::<FromNum<123>, FromNum<123>>();
/// check::<Bit0, Bit0>();
/// check::<Bit1, Bit1>();
/// ```
///
/// ```compile_fail
/// # use typebitset::rel::Equal;
/// # use typebitset::{Bit0,Bit1,FromNum};
/// # fn check<T, U: Equal<T>>(){}
/// // fails
/// check::<FromNum<123>, FromNum<456>>();
/// ```
/// ```compile_fail
/// # use typebitset::rel::Equal;
/// # use typebitset::{Bit0,Bit1,FromNum};
/// # fn check<T, U: Equal<T>>(){}
/// check::<Bit0, Bit1>();
/// ```
pub trait Equal<Rhs>: Value {}

impl Equal<Bit0> for Bit0 {}

impl Equal<Bit1> for Bit1 {}

impl<B0: Bit, B1, S0: Positive, S1> Equal<Cons<B1, S1>> for Cons<B0, S0>
where
	B1: Bit + Equal<B0>,
	S1: Positive + Equal<S0>,
{
}

/// Represents that two [`Value`] are not equal. See [`Equal`].
///
/// ```
/// # use typebitset::rel::NotEqual;
/// # use typebitset::{Bit0,Bit1,FromNum};
/// fn check<T, U: NotEqual<T>>(){}
/// check::<FromNum<13>, FromNum<6>>();
/// check::<Bit0, Bit1>();
/// ```
///
/// ```compile_fail
/// # use typebitset::rel::Equal;
/// # use typebitset::{Bit0,Bit1,FromNum};
/// # fn check<T, U: NotEqual<T>>(){}
/// // fails
/// check::<FromNum<123>, FromNum<123>>();
/// ```
/// ```compile_fail
/// # use typebitset::rel::Equal;
/// # use typebitset::{Bit0,Bit1,FromNum};
/// # fn check<T, U: NotEqual<T>>(){}
/// check::<Bit0, Bit0>();
/// ```
/// ```compile_fail
/// # use typebitset::rel::Equal;
/// # use typebitset::{Bit0,Bit1,FromNum};
/// # fn check<T, U: NotEqual<T>>(){}
/// check::<Bit1, Bit1>();
/// ```
pub trait NotEqual<Rhs> {}

impl NotEqual<Bit0> for Bit1 {}
impl NotEqual<Bit1> for Bit0 {}
impl<B: Bit, S: Positive> NotEqual<Cons<B, S>> for Bit0 {}
impl<B: Bit, S: Positive> NotEqual<Cons<B, S>> for Bit1 {}
impl<B: Bit, S: Positive> NotEqual<Bit0> for Cons<B, S> {}
impl<B: Bit, S: Positive> NotEqual<Bit1> for Cons<B, S> {}
impl<S0: Positive, S1: Positive + NotEqual<S0>> NotEqual<Cons<Bit0, S1>> for Cons<Bit0, S0> {}
impl<S0: Positive, S1: Positive + NotEqual<S0>> NotEqual<Cons<Bit1, S1>> for Cons<Bit1, S0> {}
impl<S0: Positive, S1: Positive> NotEqual<Cons<Bit0, S1>> for Cons<Bit1, S0> {}
impl<S0: Positive, S1: Positive> NotEqual<Cons<Bit1, S1>> for Cons<Bit0, S0> {}

pub trait GreaterOrEqual<Rhs>: Value {}
pub trait LessOrEqual<Rhs>: Value {}

macro_rules! impl_ord {
	(@ $name:ident [$($pnam:ident: ($($ptyp:tt$(<$tpar:ident>)*),+)),*] $typ0:ty, $typ1:ty) => {
		impl<$($pnam: $($ptyp$(<$tpar>)*+)+ Sized),*> $name<$typ0> for $typ1 {}
	};
	($([$($pnam:ident: ($($ptyp:tt$(<$tpar:ident>)*),+)),*] $typ0:ty, $typ1:ty;)*) => {
		$(
			impl_ord!(@ GreaterOrEqual [$($pnam:($($ptyp$(<$tpar>)*),+)),*] $typ0, $typ1);
			impl_ord!(@ LessOrEqual [$($pnam:($($ptyp$(<$tpar>)*),+)),*] $typ1, $typ0);
		)*
	};
}

impl_ord! {
	[] Bit0, Bit0;
	[] Bit0, Bit1;
	[] Bit1, Bit1;
	[B: (Bit), S: (Positive)] Bit0, Cons<B, S>;
	[B: (Bit), S: (Positive)] Bit1, Cons<B, S>;
	[S0: (Positive), S1: (Positive , GreaterOrEqual<S0> , NotEqual<S0>)]
		Cons<Bit1, S0>, Cons<Bit0, S1>;
	[S0: (Positive), S1: (Positive , GreaterOrEqual<S0>)]
		Cons<Bit0, S0>, Cons<Bit0, S1>;
	[S0: (Positive), S1: (Positive , GreaterOrEqual<S0>)]
		Cons<Bit0, S0>, Cons<Bit1, S1>;
	[S0: (Positive), S1: (Positive , GreaterOrEqual<S0>)]
		Cons<Bit1, S0>, Cons<Bit1, S1>;
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::test::if_impl_trait;
	use crate::{from_num, FromNum};

	fn check_equal<T, U: Equal<T>>() {}
	fn check_not_equal<T, U: NotEqual<T>>() {}
	fn check_greater_eq<T, U: GreaterOrEqual<T>>() {}
	fn check_less_eq<T, U: LessOrEqual<T>>() {}

	macro_rules! test_with_number {
		(@run eq $m:expr, $n: expr) => {
			check_equal::<FromNum<{$m}>, FromNum<{$n}>>();
			check_greater_eq::<FromNum<{$n}>, FromNum<{$m}>>();
			check_less_eq::<FromNum<{$m}>, FromNum<{$n}>>();
			assert!(!if_impl_trait!(FromNum<{$m}>: NotEqual<FromNum<{$n}>>));
			assert!(from_num::<{$m}>() == from_num::<{$n}>());
			assert!(!(from_num::<{$m}>() > from_num::<{$n}>()));
			assert!(!(from_num::<{$m}>() < from_num::<{$n}>()));
			assert!(from_num::<{$m}>() >= from_num::<{$n}>());
			assert!(from_num::<{$m}>() <= from_num::<{$n}>());
		};
		(@run neq $m:expr, $n: expr) => { // m > n
			check_not_equal::<FromNum<{$m}>, FromNum<{$n}>>();
			check_greater_eq::<FromNum<{$n}>, FromNum<{$m}>>();
			check_less_eq::<FromNum<{$m}>, FromNum<{$n}>>();
			assert!(!if_impl_trait!(FromNum<{$m}>: Equal<FromNum<{$n}>>));
			assert!(!if_impl_trait!(FromNum<{$n}>: GreaterOrEqual<FromNum<{$m}>>));
			assert!(!if_impl_trait!(FromNum<{$m}>: LessOrEqual<FromNum<{$n}>>));
			assert!(from_num::<{$m}>() != from_num::<{$n}>());
			assert!(from_num::<{$m}>() > from_num::<{$n}>());
			assert!(!(from_num::<{$m}>() <= from_num::<{$n}>()));
		};
		(@ $lbl:ident [$($ys:expr),*] [$($zs:expr),*]) => {
			test_with_number!(@run $lbl 0usize $(+$ys)*, 0usize $(+$zs)*);
		};
		(@ $lbl:ident [$($ys:expr),*] [$($zs:expr),*] $x:expr $(,$xs:expr)*) => {
			test_with_number!(@ $lbl [$($ys),*][$($zs),*]$($xs),*);
			test_with_number!(@ neq [$($ys,)*$x][$($zs),*]$($xs),*);
			test_with_number!(@ $lbl [$($ys,)*$x][$($zs,)*$x]$($xs),*);
		};
		($($xs:expr),*) => {
			test_with_number!(@ eq [] [] $($xs),*);
		};
	}
	#[test]
	fn test() {
		test_with_number!(1, 2, 4, 8, 16, 32);
	}
}
