# atomic_fn
A library which provides a generic `AtomicFnPtr<T>` type for all `T` where `T` is a 
function pointer such as `fn()` or `fn(usize) -> usize`.
Probably works, but not recommended for serious use yet.

This library always uses native atomic instructions since function pointers almost always
have the right size and alignment for atomic loads and stores. 
In case function pointers on the target platform do not have the right size or alignment 
for atomic loads and stores, the library fails to compile, and if that is bypassed, 
there are runtime guards that panic if the size or alignment is not supported.

This crate uses `#![no_std]` and only depends on libcore.

# Usage
Add this to your Cargo.toml:
```toml
[dependencies]
atomic_fn = "0.2"
```
and this to your crate root:
```rust
extern crate atomic;
```

## License
Licensed under either of

* Apache License, Version 2.0
  ([LICENSE-APACHE](LICENSE-APACHE) or [opensource.org/licenses/Apache-2.0](https://opensource.org/licenses/Apache-2.0))
* MIT License
  ([LICENSE-MIT](LICENSE-MIT) or [opensource.org/licenses/MIT](https://opensource.org/licenses/MIT))

at your option.

## Contribution
Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
