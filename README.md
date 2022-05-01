# typebitset


[![Test Status](https://github.com/yasuo-ozu/typebitset/workflows/Tests/badge.svg?event=push)](https://github.com/yasuo-ozu/typebitset/actions)
[![Crate](https://img.shields.io/crates/v/typebitset.svg)](https://crates.io/crates/typebitset)
[![Docs](https://docs.rs/typebitset/badge.svg)](https://docs.rs/typebitset)
[![Minimum rustc version](https://img.shields.io/badge/rustc-1.51+-lightgray.svg)]()

An type-level bitset

```rs
let v1: Cons<Bit1, Cons<Bit0, Bit1>> = Default::default();
let v2: Cons<Bit1, Bit1> = Default::default();
let _: Bit1 = v1 & v2;
let _: Cons<Bit1, Cons<Bit1, Bit1>> = v1 | v2;
let v4: <<Bit0 as ShiftRaising>::Output as Push<Bit1>>::Output = Default::default();
```
