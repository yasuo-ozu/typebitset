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
impl<B0: Bit, B1, S0: Positive, S1> NotEqual<Cons<B1, S1>> for Cons<B0, S0>
where
	B1: Bit + NotEqual<B0>,
	S1: Positive + NotEqual<S0>,
{
}

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
	[S0: (Positive), S1: (Positive , GreaterOrEqual<S0> , NotEqual<S0>)]
		Cons<Bit0, S0>, Cons<Bit0, S1>;
	[S0: (Positive), S1: (Positive , GreaterOrEqual<S0> , NotEqual<S0>)]
		Cons<Bit0, S0>, Cons<Bit1, S1>;
	[S0: (Positive), S1: (Positive , GreaterOrEqual<S0> , NotEqual<S0>)]
		Cons<Bit1, S0>, Cons<Bit1, S1>;
}
