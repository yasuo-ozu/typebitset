//! This module defines [`RecList`].
use crate::{
	Bit, Bit0, Bit1, Cons, Positive, Push, PushAfterMsb, ReplaceOnes, ShiftLowering, ShiftRaising,
	Value,
};
use core::fmt::Debug;
use core::hash::Hash;
use core::ops::{BitAnd, BitOr};

/// Represents a recursive tuple list of [`Value`].
/// List of `LEN = 0` is not supported.
///
/// Example:
/// - with `LEN = 1`: `FromNum<123>`
/// - with `LEN = 2`: `(FromNum<456>, FromNum<123>)`
/// - with `LEN = 3`: `(FromNum<789>, (FromNum<456>, FromNum<123>))`
pub trait RecList: Copy + Clone + Default + Eq + PartialEq + Debug + Hash {
	const LEN: usize;
}

/// Implemented on lists whose items are equal.
///
/// ```
/// # use typebitset::FromNum;
/// # use typebitset::list::SameList;
/// fn check<T: SameList>() {}
/// check::<FromNum<4>>();
/// check::<(FromNum<4>, FromNum<4>)>();
/// check::<(FromNum<4>, (FromNum<4>, FromNum<4>))>();
/// let _: FromNum<4> = <
/// 	<
/// 		(FromNum<4>, (FromNum<4>, FromNum<4>)) as SameList
/// 	>::Item as Default
/// >::default();
/// ```
pub trait SameList: RecList {
	type Item: Value;
}

/// Implemented on lists which has the same number of items of `S`.
///
/// ```
/// # use typebitset::FromNum;
/// # use typebitset::list::LengthSame;
/// fn check1<T: LengthSame<FromNum<1>>>() {}
/// fn check2<T: LengthSame<(FromNum<1>, FromNum<2>)>>() {}
/// fn check3<T: LengthSame<(FromNum<1>, (FromNum<2>, FromNum<3>))>>() {}
/// check1::<FromNum<4>>();
/// check2::<(FromNum<4>, FromNum<5>)>();
/// check3::<(FromNum<4>, (FromNum<5>, FromNum<6>))>();
/// ```
pub trait LengthSame<S: ?Sized>: RecList {}

/// Implemented on [`RecList`], all of the items are [`Positive`].
///
/// ```
/// # use typebitset::FromNum;
/// # use typebitset::list::PositiveAll;
/// fn check<T: PositiveAll>() {}
/// check::<FromNum<0b101>>();
/// check::<(FromNum<0b100>, FromNum<0b101>)>();
/// check::<(FromNum<0b010>, (FromNum<0b100>, FromNum<0b101>))>();
/// ```
///
/// ```compile_fail
/// # use typebitset::FromNum;
/// # use typebitset::list::PositiveAll;
/// # fn check<T: PositiveAll>() {}
/// // The following code fails
/// check::<FromNum<0>>();
/// ```
/// ```compile_fail
/// # use typebitset::FromNum;
/// # use typebitset::list::PositiveAll;
/// # fn check<T: PositiveAll>() {}
/// check::<(FromNum<0>, FromNum<0b101>)>();
/// ```
/// ```compile_fail
/// # use typebitset::FromNum;
/// # use typebitset::list::PositiveAll;
/// # fn check<T: PositiveAll>() {}
/// check::<(FromNum<0b010>, (FromNum<0>, FromNum<0b101>))>();
/// ```
pub trait PositiveAll: RecList {}

/// Implemented on [`RecList`], any of the items are [`Positive`].
///
/// ```
/// # use typebitset::FromNum;
/// # use typebitset::list::PositiveAny;
/// fn check<T: PositiveAny>() {}
/// check::<FromNum<0b101>>();
/// check::<(FromNum<0b0>, FromNum<0b101>)>();
/// check::<(FromNum<0b010>, (FromNum<0b0>, FromNum<0b0>))>();
/// ```
///
/// ```compile_fail
/// # use typebitset::FromNum;
/// # use typebitset::list::PositiveAny;
/// # fn check<T: PositiveAny>() {}
/// // The following code fails
/// check::<FromNum<0>>();
/// ```
/// ```compile_fail
/// # use typebitset::FromNum;
/// # use typebitset::list::PositiveAny;
/// # fn check<T: PositiveAny>() {}
/// check::<(FromNum<0>, FromNum<0b0>)>();
/// ```
/// ```compile_fail
/// # use typebitset::FromNum;
/// # use typebitset::list::PositiveAny;
/// # fn check<T: PositiveAny>() {}
/// check::<(FromNum<0b0>, (FromNum<0>, FromNum<0b0>))>();
/// ```
pub trait PositiveAny: RecList {}

impl PositiveAny for Bit1 {}
impl<B: Bit, V: Positive> PositiveAny for Cons<B, V> {}
impl<A: PositiveAny> PositiveAny for (Bit0, A) {}
impl<A: RecList> PositiveAny for (Bit1, A) {}
impl<B: Bit, V: Positive, A: RecList> PositiveAny for (Cons<B, V>, A) {}

/// Apply [`BitAnd`] to the all items in the list.
///
/// ```
/// # use typebitset::FromNum;
/// # use typebitset::list::BitAndAll;
/// let _: (FromNum<0b10>, FromNum<0b101>) = <
/// 	<
/// 		(FromNum<0b10>,FromNum<0b101>) as BitAndAll<FromNum<0b111>>
/// 	>::Output as Default
/// >::default();
/// ```
pub trait BitAndAll<S>: RecList {
	type Output: LengthSame<Self>;
	fn bitand_all(self, _: S) -> Self::Output;
}

/// Apply [`BitOr`] to the all items in the list.
///
/// ```
/// # use typebitset::FromNum;
/// # use typebitset::list::BitOrAll;
/// let _: (FromNum<0b11>, FromNum<0b101>) = <
/// 	<
/// 		(FromNum<0b10>,FromNum<0b100>) as BitOrAll<FromNum<1>>
/// 	>::Output as Default
/// >::default();
/// ```
pub trait BitOrAll<S>: RecList {
	type Output: LengthSame<Self>;
	fn bitor_all(self, _: S) -> Self::Output;
}

/// Apply [`ShiftRaising`] to the all items in the list.
///
/// ```
/// # use typebitset::FromNum;
/// # use typebitset::list::ShiftRaisingAll;
/// let _: (FromNum<0b10>, FromNum<0b100>) = <
/// 	<
/// 		(FromNum<0b1>,FromNum<0b10>) as ShiftRaisingAll
/// 	>::Output as Default
/// >::default();
/// ```
pub trait ShiftRaisingAll: RecList {
	type Output: LengthSame<Self>;
	fn shift_raising_all(self) -> Self::Output;
}

/// Apply [`ShiftLowering`] to the all items in the list.
///
/// ```
/// # use typebitset::FromNum;
/// # use typebitset::list::ShiftLoweringAll;
/// let _: (FromNum<0b1>, FromNum<0b10>) = <
/// 	<
/// 		(FromNum<0b11>,FromNum<0b101>) as ShiftLoweringAll
/// 	>::Output as Default
/// >::default();
/// ```
pub trait ShiftLoweringAll: RecList {
	type Output: LengthSame<Self>;

	/// Take the LSBs of given [`RecList`].
	///
	/// ```
	/// # use typebitset::{Bit0, Bit1, Value, FromNum};
	/// # use typebitset::list::ShiftLoweringAll;
	/// let _: (Bit0, (Bit1, Bit1)) = <<(
	/// 	FromNum<0b0>, (FromNum<0b1>, (FromNum<0b11>))
	/// ) as ShiftLoweringAll>::Lsb as Default>::default();
	/// ```
	type Lsb: LengthSame<Self> + BitList;
	fn shift_lowering_all(self) -> Self::Output;
}

/// Apply [`Push`] to the all items in the list.
///
/// ```
/// # use typebitset::{FromNum, Bit1};
/// # use typebitset::list::PushAll;
/// let _: (FromNum<0b11>, FromNum<0b101>) = <
/// 	<
/// 		(FromNum<0b1>,FromNum<0b10>) as PushAll<Bit1>
/// 	>::Output as Default
/// >::default();
/// ```
pub trait PushAll<B>: RecList {
	type Output: LengthSame<Self>;
}

/// Apply [`PushAfterMsb`] to the all items in the list.
///
/// ```
/// # use typebitset::{FromNum, Bit1};
/// # use typebitset::list::PushAfterMsbAll;
/// let _: (FromNum<0b11>, FromNum<0b110>) = <
/// 	<
/// 		(FromNum<0b1>,FromNum<0b10>) as PushAfterMsbAll<Bit1>
/// 	>::Output as Default
/// >::default();
/// ```
pub trait PushAfterMsbAll<B>: RecList {
	type Output: LengthSame<Self>;
}

/// Apply [`PushAfterMsb`] to the all items in the list.
///
/// ```
/// # use typebitset::{FromNum, Bit1};
/// # use typebitset::list::PushAfterMsbAll;
/// let _: (FromNum<0b11>, FromNum<0b110>) = <
/// 	<
/// 		(FromNum<0b1>,FromNum<0b10>) as PushAfterMsbAll<Bit1>
/// 	>::Output as Default
/// >::default();
/// ```
pub trait ReplaceOnesAll<S>: RecList {
	type Output: LengthSame<Self>;
}

/// Fold the [`RecList`] applying [`BitAnd`].
///
/// ```
/// # use typebitset::FromNum;
/// # use typebitset::list::BitAndFold;
/// let _: FromNum<0b1010> = <
/// 	<FromNum<0b1010> as BitAndFold>::Output as Default
/// >::default();
/// let _: FromNum<0b1010> = <
/// 	<
/// 		(FromNum<0b1011>,FromNum<0b1110>) as BitAndFold
/// 	>::Output as Default
/// >::default();
/// ```
pub trait BitAndFold: RecList {
	type Output: Value;
	fn bitand_fold(self) -> Self::Output;
}

/// Fold the [`RecList`] applying [`BitOr`].
///
/// ```
/// # use typebitset::FromNum;
/// # use typebitset::list::BitOrFold;
/// let _: FromNum<0b1010> = <
/// 	<
/// 		FromNum<0b1010> as BitOrFold
/// 	>::Output as Default
/// >::default();
/// let _: FromNum<0b1010> = <
/// 	<
/// 		(FromNum<0b1000>,FromNum<0b0010>) as BitOrFold
/// 	>::Output as Default
/// >::default();
/// ```
pub trait BitOrFold: RecList {
	type Output: Value;
	fn bitor_fold(self) -> Self::Output;
}

/// A [`RecList`], consisted of bits.
///
/// As differented from [`Value`] itself, it is legal that [`Bit0`] exists in
/// MSB. It means that there are multiple [`BitList`] targeted to the same
/// [`Value`].
pub trait BitList: RecList {
	/// Convert the [`BitList`] into a [`Value`].
	///
	/// ```
	/// # use typebitset::{Bit0, Bit1, Value, FromNum};
	/// # use typebitset::list::BitList;
	/// fn get_val<T: BitList>() -> T::Val {
	/// 	<T::Val as Default>::default()
	/// }
	/// let _: FromNum<0b1010> = get_val::<(Bit0, (Bit1, (Bit0, Bit1)))>();
	/// let _: FromNum<1> = get_val::<(Bit1, (Bit0, (Bit0, Bit0)))>();
	/// ```
	type Val: Value;
}

impl BitList for Bit0 {
	type Val = Bit0;
}

impl BitList for Bit1 {
	type Val = Bit1;
}

impl<B: Bit, A: BitList> BitList for (B, A)
where
	(B, A): RecList,
	(B, A::Val): Normalize,
{
	type Val = <(B, A::Val) as Normalize>::Output;
}

#[doc(hidden)]
pub trait Normalize {
	type Output: Value;
}

impl<B: Bit> Normalize for (B, Bit0) {
	type Output = B;
}

impl<B: Bit> Normalize for (B, Bit1) {
	type Output = Cons<B, Bit1>;
}

impl<B: Bit, B0: Bit, V0: Positive> Normalize for (B, Cons<B0, V0>) {
	type Output = Cons<B, Cons<B0, V0>>;
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
	(@all_nofunc [$($param0:ident),*] $trait:ident, $inner_trait:ident [$($param:ident : $tparam:ident),*] $obj:ty ) => {
		impl<$($param0,)*$($param: $tparam),*> $trait<$($param0),*> for $obj
		where
			$obj: $inner_trait<$($param0),*>,
			<$obj as $inner_trait<$($param0),*>>::Output: LengthSame<$obj> + Default,
		{
			type Output = <$obj as $inner_trait<$($param0),*>>::Output;
		}
		impl<$($param0,)*$($param: $tparam,)* A> $trait<$($param0),*> for ($obj, A)
		where
			$obj: $inner_trait<$($param0,)*>,
			A: $trait<$($param0),*>,
			(<$obj as $inner_trait<$($param0),*>>::Output, <A as $trait<$($param0),*>>::Output): LengthSame<($obj, A)> + Default,
		{
			type Output = (<$obj as $inner_trait<$($param0),*>>::Output, <A as $trait<$($param0),*>>::Output);
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

		impl<$($param: $tparam),*> SameList for $obj
		where $obj: Value,
		{
			type Item = $obj;
		}
		impl<A$(,$param: $tparam)*> SameList for ($obj, A)
		where
			A: SameList<Item = $obj>,
			$obj: Value,
		{
			type Item = $obj;
		}

		impl<$($param: $tparam),*> ShiftLoweringAll for $obj
		where
			$obj: ShiftLowering,
			<$obj as ShiftLowering>::Lsb: BitList + LengthSame<Self>,
			<$obj as ShiftLowering>::Output: LengthSame<Self>,
		{
			type Lsb = <$obj as ShiftLowering>::Lsb;
			type Output = <$obj as ShiftLowering>::Output;
			fn shift_lowering_all(self) -> Self::Output {
				Default::default()
			}
		}

		impl<A$(,$param: $tparam)*> ShiftLoweringAll for ($obj, A)
		where
			(<$obj as ShiftLowering>::Lsb, A::Lsb): BitList + LengthSame<Self>,
			(<$obj as ShiftLowering>::Output, A::Output): LengthSame<Self>,
			A: ShiftLoweringAll,
			$obj: ShiftLowering,
		{
			type Lsb = (<$obj as ShiftLowering>::Lsb, A::Lsb);
			type Output = (<$obj as ShiftLowering>::Output, A::Output);
			fn shift_lowering_all(self) -> Self::Output {
				Default::default()
			}
		}

		impl_all!(@all [S] BitAndAll, BitAnd, bitand_all [$($param: $tparam),*] $obj);
		impl_all!(@all [S] BitOrAll, BitOr, bitor_all [$($param: $tparam),*] $obj);
		impl_all!(@all [] ShiftRaisingAll, ShiftRaising, shift_raising_all [$($param: $tparam),*] $obj);
		impl_all!(@all_nofunc [Bi] PushAll, Push [$($param: $tparam),*] $obj);
		impl_all!(@all_nofunc [Bi] PushAfterMsbAll, PushAfterMsb [$($param: $tparam),*] $obj);
		impl_all!(@all_nofunc [Si] ReplaceOnesAll, ReplaceOnes [$($param: $tparam),*] $obj);
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
