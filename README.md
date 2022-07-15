# typebitset


[![Test Status](https://github.com/yasuo-ozu/typebitset/workflows/Tests/badge.svg?event=push)](https://github.com/yasuo-ozu/typebitset/actions)
[![Crate](https://img.shields.io/crates/v/typebitset.svg)](https://crates.io/crates/typebitset)
[![Docs](https://docs.rs/typebitset/badge.svg)](https://docs.rs/typebitset)
[![Minimum rustc version](https://img.shields.io/badge/rustc-1.54+-lightgray.svg)]()

An type-level number and list implementation for Rust.

## Type-level number

Type-level number is available via `FromNum<N>` (by type) or `from_num::<N>()` (by value) interface, or directly constructed using `Cons`, `Bit0` and `Bit1`.

```rs
let v1: Cons<Bit1, Cons<Bit0, Bit1>> = from_num::<5>();
let v2: Cons<Bit1, Bit1> = from_num::<3>() ;
let v3: Bit1 = v1 & v2;
println!("v3 = {}", &v3);
let v4: FromNum<7> = v1 | v2;
let v5: <<Bit0 as ShiftRaising>::Output as Push<Bit1>>::Output = Default::default();
```

All type-level number implements trait `Value`, which supports some methods to convert between type, value and `usize` number.

Some operations are supported for type-level number.

```rs
use typebitset::{FromNum, from_num, ShiftRaising, ShiftLowering};
let v1 = from_num::<7>();
let v2: FromNum<3> = v1.shift_raising();
println!("v2 = {}", &v2);
```

## Type-level list

typebitset supports type-level list, which contains type-level numbers.
Some operations are implemented on type-level list.
