use crate::{Bit, Bit0, Bit1, Cons, Positive, ShiftLowering, ShiftRaising};
use core::ops::{BitAnd, BitOr};

/// Represents a recursive list of [`Value`].
pub trait RecList {}

pub trait BitAndAll<S> {
	type Output: RecList;
	fn bitand_all(self, _: S) -> Self::Output;
}

pub trait BitOrAll<S> {
	type Output: RecList;
	fn bitor_all(self, _: S) -> Self::Output;
}

pub trait ShiftRaisingAll {
	type Output: RecList;
	fn shift_raising_all(self) -> Self::Output;
}

pub trait ShiftLoweringAll {
	type Output: RecList;
	fn shift_lowering_all(self) -> Self::Output;
}

macro_rules! impl_all {
	(@with_param $trait:ident, $inner_trait:ident, $func:ident [$($param:ident : $tparam:ident),*] $($obj:tt)+ ) => {
		impl<S$(,$param: $tparam)*> $trait<S> for $($obj)+
		where
			$($obj)+: $inner_trait<S>,
			<$($obj)+ as $inner_trait<S>>::Output: RecList + Default,
		{
			type Output = <$($obj)+ as $inner_trait<S>>::Output;
			fn $func(self, _: S) -> Self::Output {
				Default::default()
			}
		}

		impl<S, A$(,$param: $tparam)*> $trait<S> for ($($obj)+, A)
		where
			$($obj)+: $inner_trait<S>,
			A: $trait<S>,
			(<$($obj)+ as $inner_trait<S>>::Output, <A as $trait<S>>::Output): RecList + Default,
		{
			type Output = (<$($obj)+ as $inner_trait<S>>::Output, <A as $trait<S>>::Output);
			fn $func(self, _: S) -> Self::Output {
				Default::default()
			}
		}
	};
	(@ $trait:ident, $inner_trait:ident, $func:ident [$($param:ident : $tparam:ident),*] $($obj:tt)+ ) => {
		impl<$($param: $tparam),*> $trait for $($obj)+
		where
			$($obj)+: $inner_trait,
			<$($obj)+ as $inner_trait>::Output: RecList + Default,
		{
			type Output = <$($obj)+ as $inner_trait>::Output;
			fn $func(self) -> Self::Output {
				Default::default()
			}
		}

		impl<A$(,$param: $tparam)*> $trait for ($($obj)+, A)
		where
			$($obj)+: $inner_trait,
			A: $trait,
			(<$($obj)+ as $inner_trait>::Output, <A as $trait>::Output): RecList + Default,
		{
			type Output = (<$($obj)+ as $inner_trait>::Output, <A as $trait>::Output);
			fn $func(self) -> Self::Output {
				Default::default()
			}
		}
	};
	([$($param:ident : $tparam:ident),*] $($obj:tt)+ ) => {
		impl<$($param: $tparam),*> RecList for $($obj)+ {}
		impl<A: RecList$(,$param: $tparam)*> RecList for ($($obj)+, A) {}

		impl_all!(@with_param BitAndAll, BitAnd, bitand_all [$($param: $tparam),*] $($obj)+);
		impl_all!(@with_param BitOrAll, BitOr, bitor_all [$($param: $tparam),*] $($obj)+);
		impl_all!(@ ShiftRaisingAll, ShiftRaising, shift_raising_all [$($param: $tparam),*] $($obj)+);
		impl_all!(@ ShiftLoweringAll, ShiftLowering, shift_lowering_all [$($param: $tparam),*] $($obj)+);
	};
}

impl_all!([] Bit0);
impl_all!([] Bit1);
impl_all!([B: Bit, V: Positive] Cons<B, V>);
