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

/// Represents that the left [`Value`] is larger than or equal to right
/// [`Value`]. Counterpart of `>=`.
///
/// To behave as `>`, use `GreaterOrEqual<Rhs> + NotEqual<Rhs>`.
/// See [`NotEqual`]
///
/// ```
/// # use typebitset::{FromNum, rel::GreaterOrEqual, rel::NotEqual};
/// fn check_ge<T: GreaterOrEqual<U>, U>() {};
/// fn check_gt<T: GreaterOrEqual<U> + NotEqual<U>, U>() {};
/// check_ge::<FromNum<{3}>, FromNum<{2}>>();
/// check_ge::<FromNum<{3}>, FromNum<{3}>>();
/// check_gt::<FromNum<{3}>, FromNum<{2}>>();
/// ```
/// ```compile_fail
/// # use typebitset::{FromNum, rel::GreaterOrEqual, rel::NotEqual};
/// # fn check_ge<T: GreaterOrEqual<U>, U>() {};
/// # fn check_gt<T: GreaterOrEqual<U> + NotEqual<U>, U>() {};
/// // compile fails
/// check_ge::<FromNum<{2}>, FromNum<{3}>>();
/// ```
/// ```compile_fail
/// # use typebitset::{FromNum, rel::GreaterOrEqual, rel::NotEqual};
/// # fn check_ge<T: GreaterOrEqual<U>, U>() {};
/// # fn check_gt<T: GreaterOrEqual<U> + NotEqual<U>, U>() {};
/// check_gt::<FromNum<{3}>, FromNum<{3}>>();
/// ```
pub trait GreaterOrEqual<Rhs>: Value {}

/// Represents that the left [`Value`] is less than or equal to right
/// [`Value`]. Counterpart of `<=`.
///
/// To behave as `<`, use `LessOrEqual<Rhs> + NotEqual<Rhs>`.
/// See [`NotEqual`]
///
/// ```
/// # use typebitset::{FromNum, rel::LessOrEqual, rel::NotEqual};
/// fn check_le<T: LessOrEqual<U>, U>() {};
/// fn check_lt<T: LessOrEqual<U> + NotEqual<U>, U>() {};
/// check_le::<FromNum<{2}>, FromNum<{3}>>();
/// check_le::<FromNum<{3}>, FromNum<{3}>>();
/// check_lt::<FromNum<{2}>, FromNum<{3}>>();
/// ```
/// ```compile_fail
/// # use typebitset::{FromNum, rel::LessOrEqual, rel::NotEqual};
/// # fn check_le<T: LessOrEqual<U>, U>() {};
/// # fn check_lt<T: LessOrEqual<U> + NotEqual<U>, U>() {};
/// // compile fails
/// check_le::<FromNum<{3}>, FromNum<{2}>>();
/// ```
/// ```compile_fail
/// # use typebitset::{FromNum, rel::LessOrEqual, rel::NotEqual};
/// # fn check_le<T: LessOrEqual<U>, U>() {};
/// # fn check_lt<T: LessOrEqual<U> + NotEqual<U>, U>() {};
/// check_lt::<FromNum<{3}>, FromNum<{3}>>();
/// ```
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

/// Compare two given [`Value`] and give `MAX` and `MIN` of them.
///
/// `BitL`, `BitR`, `BitC` are for internal use.
///
/// ```
/// # use typebitset::{FromNum,from_num,rel::Compare};
/// let _: FromNum<{3}> = <<FromNum<{3}> as Compare<FromNum<{2}>>>::MAX as Default>::default();
/// let _: FromNum<{2}> = <<FromNum<{3}> as Compare<FromNum<{2}>>>::MIN as Default>::default();
/// ```
pub trait Compare<Rhs, BitL = (), BitR = (), BitC = ()>: Value {
	type MAX: Value;
	type MIN: Value;

	#[doc(hidden)]
	type BMAX;
	#[doc(hidden)]
	type BMIN;
}

impl<BL, BR, BC> Compare<Bit0, BL, BR, BC> for Bit0 {
	type MAX = Bit0;
	type MIN = Bit0;
	type BMAX = BC;
	type BMIN = BC;
}

impl<BL, BR, BC> Compare<Bit1, BL, BR, BC> for Bit0 {
	type MAX = Bit1;
	type MIN = Bit0;
	type BMAX = BR;
	type BMIN = BL;
}

impl<BL, BR, BC> Compare<Bit0, BL, BR, BC> for Bit1 {
	type MAX = Bit1;
	type MIN = Bit0;
	type BMAX = BL;
	type BMIN = BR;
}

impl<BL, BR, BC> Compare<Bit1, BL, BR, BC> for Bit1 {
	type MAX = Bit1;
	type MIN = Bit1;
	type BMAX = BC;
	type BMIN = BC;
}

impl<BL, BR, BC, B0: Bit, S0: Positive> Compare<Bit0, BL, BR, BC> for Cons<B0, S0> {
	type MAX = Cons<B0, S0>;
	type MIN = Bit0;
	type BMAX = BL;
	type BMIN = BR;
}

impl<BL, BR, BC, B0: Bit, S0: Positive> Compare<Bit1, BL, BR, BC> for Cons<B0, S0> {
	type MAX = Cons<B0, S0>;
	type MIN = Bit1;
	type BMAX = BL;
	type BMIN = BR;
}

impl<BL, BR, BC, B0: Bit, S0: Positive> Compare<Cons<B0, S0>, BL, BR, BC> for Bit0 {
	type MAX = Cons<B0, S0>;
	type MIN = Bit0;
	type BMAX = BR;
	type BMIN = BL;
}

impl<BL, BR, BC, B0: Bit, S0: Positive> Compare<Cons<B0, S0>, BL, BR, BC> for Bit1 {
	type MAX = Cons<B0, S0>;
	type MIN = Bit1;
	type BMAX = BR;
	type BMIN = BL;
}

impl<BL, BR, BC, S0: Positive, S1: Positive> Compare<Cons<Bit0, S1>, BL, BR, BC> for Cons<Bit0, S0>
where
	S0: Compare<S1, BL, BR, BC>,
	<S0 as Compare<S1, BL, BR, BC>>::MAX: Positive,
	<S0 as Compare<S1, BL, BR, BC>>::MIN: Positive,
{
	type MAX = Cons<Bit0, <S0 as Compare<S1, BL, BR, BC>>::MAX>;
	type MIN = Cons<Bit0, <S0 as Compare<S1, BL, BR, BC>>::MIN>;
	type BMAX = <S0 as Compare<S1, BL, BR, BC>>::BMAX;
	type BMIN = <S0 as Compare<S1, BL, BR, BC>>::BMIN;
}

impl<BL, BR, BC, S0: Positive, S1: Positive> Compare<Cons<Bit1, S1>, BL, BR, BC> for Cons<Bit1, S0>
where
	S0: Compare<S1, BL, BR, BC>,
	<S0 as Compare<S1, BL, BR, BC>>::MAX: Positive,
	<S0 as Compare<S1, BL, BR, BC>>::MIN: Positive,
{
	type MAX = Cons<Bit1, <S0 as Compare<S1, BL, BR, BC>>::MAX>;
	type MIN = Cons<Bit1, <S0 as Compare<S1, BL, BR, BC>>::MIN>;
	type BMAX = <S0 as Compare<S1, BL, BR, BC>>::BMAX;
	type BMIN = <S0 as Compare<S1, BL, BR, BC>>::BMIN;
}

impl<BL, BR, BC, S0: Positive, S1: Positive> Compare<Cons<Bit1, S1>, BL, BR, BC> for Cons<Bit0, S0>
where
	S0: Compare<S1, TagBitSet<BL, Bit0>, TagBitSet<BR, Bit1>, TagBitSet<BC, Bit0>>
		+ Compare<S1, TagBitSet<BL, Bit0>, TagBitSet<BR, Bit1>, TagBitSet<BC, Bit1>>,
	<S0 as Compare<S1, TagBitSet<BL, Bit0>, TagBitSet<BR, Bit1>, TagBitSet<BC, Bit0>>>::BMAX:
		TagBitSetImpl,
	<S0 as Compare<S1, TagBitSet<BL, Bit0>, TagBitSet<BR, Bit1>, TagBitSet<BC, Bit0>>>::BMIN:
		TagBitSetImpl,
	<S0 as Compare<S1, TagBitSet<BL, Bit0>, TagBitSet<BR, Bit1>, TagBitSet<BC, Bit0>>>::MAX:
		Positive,
	<S0 as Compare<S1, TagBitSet<BL, Bit0>, TagBitSet<BR, Bit1>, TagBitSet<BC, Bit0>>>::MIN:
		Positive,
	<S0 as Compare<S1, TagBitSet<BL, Bit0>, TagBitSet<BR, Bit1>, TagBitSet<BC, Bit1>>>::BMAX:
		TagBitSetImpl,
	<S0 as Compare<S1, TagBitSet<BL, Bit0>, TagBitSet<BR, Bit1>, TagBitSet<BC, Bit1>>>::BMIN:
		TagBitSetImpl,
	<S0 as Compare<S1, TagBitSet<BL, Bit0>, TagBitSet<BR, Bit1>, TagBitSet<BC, Bit1>>>::MAX:
		Positive,
	<S0 as Compare<S1, TagBitSet<BL, Bit0>, TagBitSet<BR, Bit1>, TagBitSet<BC, Bit1>>>::MIN:
		Positive,
{
	type MAX =
		Cons<
			<<S0 as Compare<
				S1,
				TagBitSet<BL, Bit0>,
				TagBitSet<BR, Bit1>,
				TagBitSet<BC, Bit1>,
			>>::BMAX as TagBitSetImpl>::Bit,
			<S0 as Compare<
				S1,
				TagBitSet<BL, Bit0>,
				TagBitSet<BR, Bit1>,
				TagBitSet<BC, Bit1>,
			>>::MAX,
		>;
	type MIN =
		Cons<
			<<S0 as Compare<
				S1,
				TagBitSet<BL, Bit0>,
				TagBitSet<BR, Bit1>,
				TagBitSet<BC, Bit0>,
			>>::BMIN as TagBitSetImpl>::Bit,
			<S0 as Compare<
				S1,
				TagBitSet<BL, Bit0>,
				TagBitSet<BR, Bit1>,
				TagBitSet<BC, Bit0>,
			>>::MIN,
		>;
	type BMAX = <<S0 as Compare<
		S1,
		TagBitSet<BL, Bit0>,
		TagBitSet<BR, Bit1>,
		TagBitSet<BC, Bit1>,
	>>::BMAX as TagBitSetImpl>::Tag;
	type BMIN = <<S0 as Compare<
		S1,
		TagBitSet<BL, Bit0>,
		TagBitSet<BR, Bit1>,
		TagBitSet<BC, Bit0>,
	>>::BMIN as TagBitSetImpl>::Tag;
}

impl<BL, BR, BC, S0: Positive, S1: Positive> Compare<Cons<Bit0, S1>, BL, BR, BC> for Cons<Bit1, S0>
where
	S0: Compare<S1, TagBitSet<BL, Bit1>, TagBitSet<BR, Bit0>, TagBitSet<BC, Bit0>>
		+ Compare<S1, TagBitSet<BL, Bit1>, TagBitSet<BR, Bit0>, TagBitSet<BC, Bit1>>,
	<S0 as Compare<S1, TagBitSet<BL, Bit1>, TagBitSet<BR, Bit0>, TagBitSet<BC, Bit0>>>::BMAX:
		TagBitSetImpl,
	<S0 as Compare<S1, TagBitSet<BL, Bit1>, TagBitSet<BR, Bit0>, TagBitSet<BC, Bit0>>>::BMIN:
		TagBitSetImpl,
	<S0 as Compare<S1, TagBitSet<BL, Bit1>, TagBitSet<BR, Bit0>, TagBitSet<BC, Bit0>>>::MAX:
		Positive,
	<S0 as Compare<S1, TagBitSet<BL, Bit1>, TagBitSet<BR, Bit0>, TagBitSet<BC, Bit0>>>::MIN:
		Positive,
	<S0 as Compare<S1, TagBitSet<BL, Bit1>, TagBitSet<BR, Bit0>, TagBitSet<BC, Bit1>>>::BMAX:
		TagBitSetImpl,
	<S0 as Compare<S1, TagBitSet<BL, Bit1>, TagBitSet<BR, Bit0>, TagBitSet<BC, Bit1>>>::BMIN:
		TagBitSetImpl,
	<S0 as Compare<S1, TagBitSet<BL, Bit1>, TagBitSet<BR, Bit0>, TagBitSet<BC, Bit1>>>::MAX:
		Positive,
	<S0 as Compare<S1, TagBitSet<BL, Bit1>, TagBitSet<BR, Bit0>, TagBitSet<BC, Bit1>>>::MIN:
		Positive,
{
	type MAX =
		Cons<
			<<S0 as Compare<
				S1,
				TagBitSet<BL, Bit1>,
				TagBitSet<BR, Bit0>,
				TagBitSet<BC, Bit1>,
			>>::BMAX as TagBitSetImpl>::Bit,
			<S0 as Compare<
				S1,
				TagBitSet<BL, Bit1>,
				TagBitSet<BR, Bit0>,
				TagBitSet<BC, Bit1>,
			>>::MAX,
		>;
	type MIN =
		Cons<
			<<S0 as Compare<
				S1,
				TagBitSet<BL, Bit1>,
				TagBitSet<BR, Bit0>,
				TagBitSet<BC, Bit0>,
			>>::BMIN as TagBitSetImpl>::Bit,
			<S0 as Compare<
				S1,
				TagBitSet<BL, Bit1>,
				TagBitSet<BR, Bit0>,
				TagBitSet<BC, Bit0>,
			>>::MIN,
		>;
	type BMAX = <<S0 as Compare<
		S1,
		TagBitSet<BL, Bit1>,
		TagBitSet<BR, Bit0>,
		TagBitSet<BC, Bit1>,
	>>::BMAX as TagBitSetImpl>::Tag;
	type BMIN = <<S0 as Compare<
		S1,
		TagBitSet<BL, Bit1>,
		TagBitSet<BR, Bit0>,
		TagBitSet<BC, Bit0>,
	>>::BMIN as TagBitSetImpl>::Tag;
}

/// Given two [`Value`]s, retuens larger one.
///
/// ```
/// # use typebitset::{FromNum, from_num, rel::max};
/// let _: FromNum<{12}> = max(&from_num::<{3}>(), &from_num::<{12}>());
/// let _: FromNum<{3}> = max(&from_num::<{3}>(), &from_num::<{3}>());
/// ```
pub fn max<V0, V1>(_: &V0, _: &V1) -> <V0 as Compare<V1>>::MAX
where
	V0: Compare<V1>,
{
	Default::default()
}

/// Given two [`Value`]s, retuens smaller one.
///
/// ```
/// # use typebitset::{FromNum, from_num, rel::min};
/// let _: FromNum<{3}> = min(&from_num::<{3}>(), &from_num::<{12}>());
/// let _: FromNum<{3}> = min(&from_num::<{3}>(), &from_num::<{3}>());
/// ```
pub fn min<V0, V1>(_: &V0, _: &V1) -> <V0 as Compare<V1>>::MIN
where
	V0: Compare<V1>,
{
	Default::default()
}

#[doc(hidden)]
pub struct TagBitSet<Tag, Bit>(core::marker::PhantomData<(Tag, Bit)>);

#[doc(hidden)]
pub trait TagBitSetImpl {
	type Tag;
	type Bit: Bit;
}

impl<L, R: Bit> TagBitSetImpl for TagBitSet<L, R> {
	type Tag = L;
	type Bit = R;
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
			let _: FromNum<{$m}> = max(&from_num::<{$m}>(), &from_num::<{$m}>());
			let _: FromNum<{$m}> = min(&from_num::<{$m}>(), &from_num::<{$m}>());
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
			let _: FromNum<{$m}> = max(&from_num::<{$m}>(), &from_num::<{$n}>());
			let _: FromNum<{$m}> = max(&from_num::<{$n}>(), &from_num::<{$m}>());
			let _: FromNum<{$n}> = min(&from_num::<{$n}>(), &from_num::<{$m}>());
			let _: FromNum<{$n}> = min(&from_num::<{$n}>(), &from_num::<{$m}>());
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
		test_with_number!(1, 2, 4, 8, 16);
	}
}
