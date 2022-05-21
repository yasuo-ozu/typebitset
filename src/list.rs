use crate::{Bit, Bit0, Bit1, Cons, Positive, ShiftLowering, ShiftRaising, Value};
use core::ops::{BitAnd, BitOr};

/// Represents a recursive list of [`Value`].
pub trait RecList {
	const LEN: usize;
}

pub trait SameList<V>: RecList {}

pub trait LengthSame<S: ?Sized>: RecList {}

pub trait PositiveAll: RecList {}

pub trait BitAndAll<S>: RecList {
	type Output: LengthSame<Self>;
	fn bitand_all(self, _: S) -> Self::Output;
}

pub trait BitOrAll<S>: RecList {
	type Output: LengthSame<Self>;
	fn bitor_all(self, _: S) -> Self::Output;
}

pub trait ShiftRaisingAll: RecList {
	type Output: LengthSame<Self>;
	fn shift_raising_all(self) -> Self::Output;
}

pub trait ShiftLoweringAll: RecList {
	type Output: LengthSame<Self>;
	fn shift_lowering_all(self) -> Self::Output;
}

pub trait BitAndFold: RecList {
	type Output: Value;
	fn bitand_fold(self) -> Self::Output;
}

pub trait BitOrFold: RecList {
	type Output: Value;
	fn bitor_fold(self) -> Self::Output;
}

macro_rules! impl_all {
	(@all [$($param0:ident),*] $trait:ident, $inner_trait:ident, $func:ident [$($param:ident : $tparam:ident),*] $obj:ty ) => {
		impl<$($param0,)*$($param: $tparam),*> $trait<$($param0),*> for $obj
		where
			$obj: $inner_trait<$($param0),*>,
			<$obj as $inner_trait<$($param0),*>>::Output: LengthSame<$obj> + Default,
		{
			type Output = <$obj as $inner_trait<$($param0),*>>::Output;
			fn $func(self$(, _: $param0)*) -> Self::Output {
				Default::default()
			}
		}
		impl<$($param0,)*$($param: $tparam,)* A> $trait<$($param0),*> for ($obj, A)
		where
			$obj: $inner_trait<$($param0,)*>,
			A: $trait<$($param0),*>,
			(<$obj as $inner_trait<$($param0),*>>::Output, <A as $trait<$($param0),*>>::Output): LengthSame<($obj, A)> + Default,
		{
			type Output = (<$obj as $inner_trait<$($param0),*>>::Output, <A as $trait<$($param0),*>>::Output);
			fn $func(self$(, _: $param0)*) -> Self::Output {
				Default::default()
			}
		}
	};
	(@fold $trait:ident, $inner_trait:ident, $func:ident [$($param:ident : $tparam:ident),*] $obj:ty ) => {
		impl<$($param: $tparam),*> $trait for $obj
		{
			type Output = $obj;
			fn $func(self) -> Self::Output {
				Default::default()
			}
		}
		impl<$($param: $tparam,)* A> $trait for ($obj, A)
		where
			$obj: $inner_trait<<A as $trait>::Output>,
			A: $trait,
			<$obj as $inner_trait<<A as $trait>::Output>>::Output: Value,
		{
			type Output = <$obj as $inner_trait<<A as $trait>::Output>>::Output;
			fn $func(self) -> Self::Output {
				Default::default()
			}
		}
	};
	([$($param:ident : $tparam:ident),*] $obj:ty ) => {
		impl<$($param: $tparam),*> RecList for $obj {
			const LEN: usize = 1;
		}
		impl<A: RecList$(,$param: $tparam)*> RecList for ($obj, A) {
			const LEN: usize = <A as RecList>::LEN + 1;
		}

		impl<$($param: $tparam),*> SameList<$obj> for $obj {}
		impl<A: SameList<$obj>$(,$param: $tparam)*> SameList<$obj> for ($obj, A) {}

		impl_all!(@all [S] BitAndAll, BitAnd, bitand_all [$($param: $tparam),*] $obj);
		impl_all!(@all [S] BitOrAll, BitOr, bitor_all [$($param: $tparam),*] $obj);
		impl_all!(@all [] ShiftRaisingAll, ShiftRaising, shift_raising_all [$($param: $tparam),*] $obj);
		impl_all!(@all [] ShiftLoweringAll, ShiftLowering, shift_lowering_all [$($param: $tparam),*] $obj);
		impl_all!(@fold BitAndFold, BitAnd, bitand_fold [$($param: $tparam),*] $obj);
		impl_all!(@fold BitOrFold, BitOr, bitor_fold [$($param: $tparam),*] $obj);
	};
}

macro_rules! impl_same {
	(@
		[$($param0:ident : $tparam0:ident),*] $obj0:ty;
		[$($param1:ident : $tparam1:ident),*] $obj1:ty
	) => {
		impl<$($param0: $tparam0,)* $($param1: $tparam1),*> LengthSame<$obj0> for $obj1 {}
		impl<$($param0: $tparam0,)* $($param1: $tparam1,)* B: RecList, A: LengthSame<B>> LengthSame<($obj0, A)> for ($obj1, B) {}
	};
	(
		[$($param0:ident : $tparam0:ident),*] $obj0:ty
	) => {
		impl_same!(@ [$($param0 : $tparam0),*] $obj0; [] Bit0);
		impl_same!(@ [$($param0 : $tparam0),*] $obj0; [] Bit1);
		impl_same!(@ [$($param0 : $tparam0),*] $obj0; [B1: Bit, V1: Positive] Cons<B1, V1>);
	};
}

macro_rules! impl_positive_all {
	([$($param:ident : $tparam:ident),*] $obj:ty ) => {
		impl<$($param: $tparam),*> PositiveAll for $obj
		where
			$obj: Positive
		{}

		impl<A: PositiveAll$(,$param: $tparam)*> PositiveAll for ($obj, A)
		where
			$obj: Positive
		{}
	};
}

impl_all!([] Bit0);
impl_all!([] Bit1);
impl_all!([B: Bit, V: Positive] Cons<B, V>);

impl_positive_all!([] Bit1);
impl_positive_all!([B: Bit, V: Positive] Cons<B, V>);

impl_same!([] Bit0);
impl_same!([] Bit1);
impl_same!([B0: Bit, V0: Positive] Cons<B0, V0>);
