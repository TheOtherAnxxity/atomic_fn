#![no_std]

//! A small, no_std crate that adds atomic function pointers.
//! See [`AtomicFnPtr`] for examples.

mod impls;

use core::fmt::{self, Debug, Formatter, Pointer};
use core::panic::RefUnwindSafe;
use core::sync::atomic::Ordering;

use impls::AtomicFnInner;
use impls::AtomicFnInnerRaw;
use impls::FnPtrSealed;

/// A function pointer type which can be safely shared between threads.
///
/// This type has the same in-memory representation as a `fn()`.
///
/// **Note**: This type is only available on platforms that support atomic
/// loads and stores of u16, u32, u64, usize, or pointers.
///
/// # Compatibility with other atomics
///
/// This type is not guaranteed to be alignment or ABI-compatible with any other
/// atomic function pointer type, including in C or C++.
///
/// # Function pointers vs function item types
///
/// A `fn()` function pointer and the name of a `fn foo {}` are not the same
/// type: the latter is zero-sized and statically dispatches when called, but
/// coerces to a compatible `fn()`. A function pointer dynamically dispatches.
///
/// Because this type works with function pointers, avoid constructing an
/// `AtomicFnPtr` with a function item type - most methods will not work.
#[repr(C)]
pub struct AtomicFnPtr<T: FnPtr> {
    // Ensures that `inner` is aligned for the held `fn` as well.
    _align: [T; 0],
    inner: AtomicFnInner,
}

impl<T: FnPtr> AtomicFnPtr<T> {
    /// Creates a new `AtomicFnPtr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_fn::AtomicFnPtr;
    ///
    /// fn add_one(x: i32) -> i32 {
    ///     x + 1
    /// }
    ///
    /// let ptr: fn(i32) -> i32 = add_one;
    /// let atomic = AtomicFnPtr::new(ptr);
    /// assert_eq!((atomic.into_inner())(5), 6);
    /// ```
    #[inline]
    pub fn new(fn_ptr: T) -> AtomicFnPtr<T> {
        AtomicFnPtr {
            _align: [],
            inner: AtomicFnInner::new(fn_ptr.to_raw()),
        }
    }

    /// Consumes the atomic and returns the contained value.
    ///
    /// This is safe because passing `self` by value guarantees that no other threads are
    /// concurrently accessing the atomic data.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_fn::AtomicFnPtr;
    ///
    /// fn add_one(x: i32) -> i32 {
    ///     x + 1
    /// }
    ///
    /// let ptr: fn(i32) -> i32 = add_one;
    /// let atomic = AtomicFnPtr::new(ptr);
    /// assert_eq!((atomic.into_inner())(5), 6);
    /// ```
    #[inline]
    pub fn into_inner(self) -> T {
        // SAFETY: `self.inner` stores a valid instance of `T`.
        unsafe { T::from_raw(self.inner.into_inner()) }
    }

    /// Returns a mutable reference to the underlying pointer.
    ///
    /// This is safe because the mutable reference guarantees that no other threads are
    /// concurrently accessing the atomic data.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_fn::AtomicFnPtr;
    ///
    /// fn add_one(x: i32) -> i32 {
    ///     x + 1
    /// }
    ///
    /// fn double(x: i32) -> i32 {
    ///     x * 2
    /// }
    ///
    /// let mut atomic = AtomicFnPtr::new(add_one as fn(i32) -> i32);
    /// *atomic.get_mut() = double;
    /// assert_eq!((atomic.into_inner())(5), 10);
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        let inner_as_ptr: *mut AtomicFnInnerRaw = self.inner.get_mut();
        let inner_as_fn: *mut T = inner_as_ptr.cast();
        // SAFETY:
        // - `inner` is aligned for `T` due to `self._align`.
        // - `self.inner` stores a valid instance of `T`.
        // - `AtomicFnInnerRaw` is guaranteed to be the same size as `T`.
        // - None of the possible types for `AtomicFnInnerRaw` have a stricter
        //   bit validity requirement than `T`.
        unsafe { &mut *inner_as_fn }
    }
}

#[allow(unused_variables)]
impl<T: FnPtr> AtomicFnPtr<T> {
    /// Loads a value from the pointer.
    ///
    /// `load` takes an [`Ordering`] argument which describes the memory ordering
    /// of this operation. Possible values are [`Ordering::SeqCst`], [`Ordering::Acquire`] and [`Ordering::Relaxed`].
    ///
    /// # Panics
    ///
    /// Panics if `order` is [`Ordering::Release`] or [`Ordering::AcqRel`].
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_fn::AtomicFnPtr;
    /// use std::sync::atomic::Ordering;
    ///
    /// fn add_one(x: i32) -> i32 {
    ///     x + 1
    /// }
    ///
    /// let ptr: fn(i32) -> i32 = add_one;
    /// let atomic = AtomicFnPtr::new(ptr);
    /// assert_eq!((atomic.load(Ordering::Relaxed))(5), 6);
    /// ```
    pub fn load(&self, order: Ordering) -> T {
        let raw = self.inner.load(order);
        // SAFETY: `self.inner` stores a valid instance of `T`.
        unsafe { T::from_raw(raw) }
    }

    /// Stores a value into the pointer.
    ///
    /// `store` takes an [`Ordering`] argument which describes the memory ordering
    /// of this operation. Possible values are [`Ordering::SeqCst`], [`Ordering::Release`] and [`Ordering::Relaxed`].
    ///
    /// # Panics
    ///
    /// Panics if `order` is [`Ordering::Acquire`] or [`Ordering::AcqRel`].
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_fn::AtomicFnPtr;
    /// use std::sync::atomic::Ordering;
    ///
    /// fn add_one(x: i32) -> i32 {
    ///     x + 1
    /// }
    ///
    /// fn double(x: i32) -> i32 {
    ///     x * 2
    /// }
    ///
    /// let ptr: fn(i32) -> i32 = add_one;
    /// let atomic = AtomicFnPtr::new(ptr);
    /// assert_eq!((atomic.load(Ordering::Relaxed))(5), 6);
    /// atomic.store(double, Ordering::Relaxed);
    /// assert_eq!((atomic.load(Ordering::Relaxed))(5), 10);
    /// ```
    pub fn store(&self, fn_ptr: T, order: Ordering) {
        self.inner.store(fn_ptr.to_raw(), order);
    }

    /// Stores a value into the pointer, returning the previous value.
    ///
    /// `swap` takes an [`Ordering`] argument which describes the memory ordering
    /// of this operation. All ordering modes are possible. Note that using
    /// [`Ordering::Acquire`] makes the store part of this operation [`Ordering::Relaxed`], and
    /// using [`Ordering::Release`] makes the load part [`Ordering::Relaxed`].
    ///
    /// **Note:** This method is only available on platforms that support atomic
    /// operations on pointers.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_fn::AtomicFnPtr;
    /// use std::sync::atomic::Ordering;
    ///
    /// fn add_one(x: i32) -> i32 {
    ///     x + 1
    /// }
    ///
    /// fn double(x: i32) -> i32 {
    ///     x * 2
    /// }
    ///
    /// let ptr: fn(i32) -> i32 = add_one;
    /// let atomic = AtomicFnPtr::new(ptr);
    /// let old = atomic.swap(double, Ordering::Relaxed);
    /// assert_eq!(old(5), 6);
    /// assert_eq!((atomic.load(Ordering::Relaxed))(5), 10);
    /// ```
    pub fn swap(&self, fn_ptr: T, order: Ordering) -> T {
        let old_raw = self.inner.swap(fn_ptr.to_raw(), order);
        // SAFETY: `self.inner` stores a valid instance of `T`.
        unsafe { T::from_raw(old_raw) }
    }

    /// Stores a value into the pointer if the current value is the same as the `current` value.
    ///
    /// The return value is always the previous value. If it is equal to `current`, then the value
    /// was updated.
    ///
    /// `compare_and_swap` also takes an [`Ordering`] argument which describes the memory
    /// ordering of this operation. Notice that even when using [`Ordering::AcqRel`], the operation
    /// might fail and hence just perform an [`Ordering::Acquire`] load, but not have [`Ordering::Release`] semantics.
    /// Using [`Ordering::Acquire`] makes the store part of this operation [`Ordering::Relaxed`] if it
    /// happens, and using [`Ordering::Release`] makes the load part [`Ordering::Relaxed`].
    ///
    /// **Note:** This method is only available on platforms that support atomic
    /// operations on function pointer-sized types.
    ///
    /// # Migrating to `compare_exchange` and `compare_exchange_weak`
    ///
    /// `compare_and_swap` is equivalent to `compare_exchange` with the following mapping for
    /// memory orderings:
    ///
    ///  Original  |  Success  |  Failure
    /// ---------- | --------- | ---------
    ///  `Relaxed` | `Relaxed` | `Relaxed`
    ///  `Acquire` | `Acquire` | `Acquire`
    ///  `Release` | `Release` | `Relaxed`
    ///  `AcqRel`  | `AcqRel`  | `Acquire`
    ///  `SeqCst`  | `SeqCst`  | `SeqCst`
    ///
    /// `compare_exchange_weak` is allowed to fail spuriously even when the comparison succeeds,
    /// which allows the compiler to generate better assembly code when the compare and swap
    /// is used in a loop.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_fn::AtomicFnPtr;
    /// use std::sync::atomic::Ordering;
    ///
    /// fn a_fn(x: i32) -> i32 {
    ///     x + 1
    /// }
    ///
    /// fn another_fn(x: i32) -> i32 {
    ///     x * 2
    /// }
    ///
    /// let ptr: fn(i32) -> i32 = a_fn;
    /// let some_ptr = AtomicFnPtr::new(ptr);
    /// let other_ptr: fn(i32) -> i32 = another_fn;
    ///
    /// assert_eq!((some_ptr.load(Ordering::Relaxed))(10), 11);
    ///
    /// let value = some_ptr.compare_and_swap(ptr, other_ptr, Ordering::Relaxed);
    ///
    /// assert_eq!((some_ptr.load(Ordering::Relaxed))(10), 20);
    /// ```
    #[deprecated(
        since = "0.1.0",
        note = "\
        Use `compare_exchange` or `compare_exchange_weak` instead. \
        Only exists for compatibility with applications that use `compare_and_swap` on the `core` atomic types.\
        "
    )]
    pub fn compare_and_swap(&self, current: T, new: T, order: Ordering) -> T {
        #[allow(deprecated)]
        let raw = self
            .inner
            .compare_and_swap(current.to_raw(), new.to_raw(), order);
        // SAFETY: `self.inner` stores a valid instance of `T`.
        unsafe { T::from_raw(raw) }
    }

    /// Stores a value into the pointer if the current value is the same as the `current` value.
    ///
    /// The return value is a result indicating whether the new value was written and containing
    /// the previous value. On success this value is guaranteed to be equal to `current`.
    ///
    /// `compare_exchange` takes two [`Ordering`] arguments to describe the memory
    /// ordering of this operation. `success` describes the required ordering for the
    /// read-modify-write operation that takes place if the comparison with `current` succeeds.
    /// `failure` describes the required ordering for the load operation that takes place when
    /// the comparison fails. Using [`Ordering::Acquire`] as success ordering makes the store part
    /// of this operation [`Ordering::Relaxed`], and using [`Ordering::Release`] makes the successful load
    /// [`Ordering::Relaxed`]. The failure ordering can only be [`Ordering::SeqCst`], [`Ordering::Acquire`] or [`Ordering::Relaxed`]
    /// and must be equivalent to or weaker than the success ordering.
    ///
    /// **Note:** This method is only available on platforms that support atomic
    /// operations on pointers.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::atomic::Ordering;
    /// use atomic_fn::AtomicFnPtr;
    ///
    /// fn add_one(x: i32) -> i32 {
    ///     x + 1
    /// }
    ///
    /// fn double(x: i32) -> i32 {
    ///     x * 2
    /// }
    ///
    /// let ptr: fn(i32) -> i32 = add_one;
    /// let some_ptr = AtomicFnPtr::new(ptr);
    /// let other_ptr: fn(i32) -> i32 = double;
    ///
    /// assert_eq!((some_ptr.load(Ordering::SeqCst))(5), 6);
    ///
    /// let value = some_ptr.compare_exchange(
    ///     ptr,
    ///     other_ptr,
    ///     Ordering::SeqCst,
    ///     Ordering::Relaxed,
    /// );
    ///
    /// assert_eq!(value, Ok(ptr));
    /// assert_eq!((some_ptr.load(Ordering::SeqCst))(5), 10);
    /// ```
    pub fn compare_exchange(
        &self,
        current: T,
        new: T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<T, T> {
        let result = self
            .inner
            .compare_exchange(current.to_raw(), new.to_raw(), success, failure);
        // SAFETY: `self.inner` stores a valid instance of `T`.
        unsafe {
            match result {
                Ok(raw) => Ok(T::from_raw(raw)),
                Err(raw) => Err(T::from_raw(raw)),
            }
        }
    }

    /// Stores a value into the pointer if the current value is the same as the `current` value.
    ///
    /// Unlike [`AtomicFnPtr::compare_exchange`], this function is allowed to spuriously fail even when the
    /// comparison succeeds, which can result in more efficient code on some platforms. The
    /// return value is a result indicating whether the new value was written and containing the
    /// previous value.
    ///
    /// `compare_exchange_weak` takes two [`Ordering`] arguments to describe the memory
    /// ordering of this operation. `success` describes the required ordering for the
    /// read-modify-write operation that takes place if the comparison with `current` succeeds.
    /// `failure` describes the required ordering for the load operation that takes place when
    /// the comparison fails. Using [`Ordering::Acquire`] as success ordering makes the store part
    /// of this operation [`Ordering::Relaxed`], and using [`Ordering::Release`] makes the successful load
    /// [`Ordering::Relaxed`]. The failure ordering can only be [`Ordering::SeqCst`], [`Ordering::Acquire`] or [`Ordering::Relaxed`]
    /// and must be equivalent to or weaker than the success ordering.
    ///
    /// **Note:** This method is only available on platforms that support atomic
    /// operations on pointers.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_fn::AtomicFnPtr;
    /// use std::sync::atomic::Ordering;
    ///
    /// fn add_one(x: i32) -> i32 {
    ///     x + 1
    /// }
    ///
    /// fn double(x: i32) -> i32 {
    ///     x * 2
    /// }
    ///
    /// let some_ptr = AtomicFnPtr::new(add_one as fn(i32) -> i32);
    /// let new: fn(i32) -> i32 = double;
    /// let mut old = some_ptr.load(Ordering::Relaxed);
    ///
    /// assert_eq!(old(5), 6);
    ///
    /// loop {
    ///     match some_ptr.compare_exchange_weak(old, new, Ordering::SeqCst, Ordering::Relaxed) {
    ///         Ok(x) => {
    ///             assert_eq!(x(5), 6);
    ///             break;
    ///         }
    ///         Err(x) => {
    ///             assert_eq!(x(5), 6);
    ///             old = x;
    ///         }
    ///     }
    /// }
    ///
    /// assert_eq!((some_ptr.load(Ordering::Relaxed))(5), 10);
    /// ```
    pub fn compare_exchange_weak(
        &self,
        current: T,
        new: T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<T, T> {
        let result =
            self.inner
                .compare_exchange_weak(current.to_raw(), new.to_raw(), success, failure);
        // SAFETY: `self.inner` stores a valid instance of `T`.
        unsafe {
            match result {
                Ok(raw) => Ok(T::from_raw(raw)),
                Err(raw) => Err(T::from_raw(raw)),
            }
        }
    }

    /// Fetches the value, and applies a function to it that returns an optional
    /// new value. Returns a `Result` of `Ok(previous_value)` if the function
    /// returned `Some(_)`, else `Err(previous_value)`.
    ///
    /// Note: This may call the function multiple times if the value has been
    /// changed from other threads in the meantime, as long as the function
    /// returns `Some(_)`, but the function will have been applied only once to
    /// the stored value.
    ///
    /// `fetch_update` takes two [`Ordering`] arguments to describe the memory
    /// ordering of this operation. The first describes the required ordering for
    /// when the operation finally succeeds while the second describes the
    /// required ordering for loads. These correspond to the success and failure
    /// orderings of [`AtomicFnPtr::compare_exchange`] respectively.
    ///
    /// Using [`Ordering::Acquire`] as success ordering makes the store part of this
    /// operation [`Ordering::Relaxed`], and using [`Ordering::Release`] makes the final successful
    /// load [`Ordering::Relaxed`]. The (failed) load ordering can only be [`Ordering::SeqCst`],
    /// [`Ordering::Acquire`] or [`Ordering::Relaxed`] and must be equivalent to or weaker than the
    /// success ordering.
    ///
    /// **Note:** This method is only available on platforms that support atomic
    /// operations on pointers.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[allow(clippy::fn_address_comparisons)]
    /// use atomic_fn::AtomicFnPtr;
    /// use std::sync::atomic::Ordering;
    ///
    /// fn add_one(x: i32) -> i32 {
    ///     x + 1
    /// }
    ///
    /// fn double(x: i32) -> i32 {
    ///     x * 2
    /// }
    ///
    /// let ptr: fn(i32) -> i32 = add_one;
    /// let some_ptr = AtomicFnPtr::new(ptr);
    /// let new: fn(i32) -> i32 = double;
    ///
    /// assert_eq!(some_ptr.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |_| None), Err(ptr));
    /// assert_eq!((some_ptr.load(Ordering::SeqCst))(5), 6);
    /// let result = some_ptr.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |x| {
    ///     if x == ptr {
    ///         Some(new)
    ///     } else {
    ///         None
    ///     }
    /// });
    /// assert_eq!(result, Ok(ptr));
    /// assert_eq!((some_ptr.load(Ordering::SeqCst))(5), 10);
    /// assert_eq!(some_ptr.load(Ordering::SeqCst), new);
    /// ```
    pub fn fetch_update<F>(
        &self,
        set_order: Ordering,
        fetch_order: Ordering,
        mut func: F,
    ) -> Result<T, T>
    where
        F: FnMut(T) -> Option<T>,
    {
        let result = self.inner.fetch_update(set_order, fetch_order, move |raw| {
            // SAFETY: `self.inner` stores a valid instance of `T`.
            func(unsafe { T::from_raw(raw) }).map(|fn_ptr| fn_ptr.to_raw())
        });
        // SAFETY: `self.inner` stores a valid instance of `T`.
        unsafe {
            match result {
                Ok(raw) => Ok(T::from_raw(raw)),
                Err(raw) => Err(T::from_raw(raw)),
            }
        }
    }
}

impl<T: FnPtr> From<T> for AtomicFnPtr<T> {
    #[inline]
    fn from(fn_ptr: T) -> AtomicFnPtr<T> {
        AtomicFnPtr::new(fn_ptr)
    }
}

impl<T: FnPtr + Debug> Debug for AtomicFnPtr<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // This is the same inner code as AtomicPtr::fmt
        // This is only done this way in case
        // the formatting of function pointers and data pointers diverges
        Debug::fmt(&self.load(Ordering::SeqCst), f)
    }
}

impl<T: FnPtr + Pointer> Pointer for AtomicFnPtr<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // This is the same inner code as AtomicPtr::fmt
        // This is only done this way in case
        // the formatting of function pointers and data pointers diverges
        Pointer::fmt(&self.load(Ordering::SeqCst), f)
    }
}

// SAFETY: We only access the memory atomically
unsafe impl<T: FnPtr + Sync> Sync for AtomicFnPtr<T> {}

// SAFETY: We only access the memory atomically
impl<T: FnPtr + RefUnwindSafe> RefUnwindSafe for AtomicFnPtr<T> {}

pub trait FnPtr: Copy + FnPtrSealed /* Eq + Ord + Hash + Pointer + Debug */ {
    // Empty
}

#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;
    use core::sync::atomic::Ordering;

    fn add_one(x: i32) -> i32 {
        x + 1
    }

    fn double(x: i32) -> i32 {
        x * 2
    }

    #[test]
    fn option_new_some_into_inner() {
        let f: Option<fn(i32) -> i32> = Some(add_one);
        let atomic = AtomicFnPtr::new(f);
        assert_eq!(atomic.into_inner().unwrap()(5), 6);
    }

    #[test]
    fn option_new_none_into_inner() {
        let f: Option<fn(i32) -> i32> = None;
        let atomic = AtomicFnPtr::new(f);
        assert!(atomic.into_inner().is_none());
    }

    #[test]
    fn option_load_some() {
        let atomic = AtomicFnPtr::new(Some(add_one as fn(i32) -> i32));
        assert_eq!(atomic.load(Ordering::SeqCst).unwrap()(10), 11);
    }

    #[test]
    fn option_load_none() {
        let atomic: AtomicFnPtr<Option<fn(i32) -> i32>> = AtomicFnPtr::new(None);
        assert!(atomic.load(Ordering::SeqCst).is_none());
    }

    #[test]
    fn option_store_none_then_some() {
        let atomic: AtomicFnPtr<Option<fn(i32) -> i32>> = AtomicFnPtr::new(None);
        assert!(atomic.load(Ordering::SeqCst).is_none());
        atomic.store(Some(double), Ordering::SeqCst);
        assert_eq!(atomic.load(Ordering::SeqCst).unwrap()(5), 10);
    }

    #[test]
    fn option_store_some_then_none() {
        let atomic = AtomicFnPtr::new(Some(add_one as fn(i32) -> i32));
        atomic.store(None, Ordering::SeqCst);
        assert!(atomic.load(Ordering::SeqCst).is_none());
    }

    #[test]
    fn option_swap_some_to_none() {
        let atomic = AtomicFnPtr::new(Some(add_one as fn(i32) -> i32));
        let old = atomic.swap(None, Ordering::SeqCst);
        assert_eq!(old.unwrap()(3), 4);
        assert!(atomic.load(Ordering::SeqCst).is_none());
    }

    #[test]
    fn option_swap_none_to_some() {
        let atomic: AtomicFnPtr<Option<fn(i32) -> i32>> = AtomicFnPtr::new(None);
        let old = atomic.swap(Some(double), Ordering::SeqCst);
        assert!(old.is_none());
        assert_eq!(atomic.load(Ordering::SeqCst).unwrap()(3), 6);
    }

    #[test]
    fn option_get_mut_some_to_none() {
        let mut atomic = AtomicFnPtr::new(Some(add_one as fn(i32) -> i32));
        *atomic.get_mut() = None;
        assert!(atomic.into_inner().is_none());
    }

    #[test]
    fn option_get_mut_none_to_some() {
        let mut atomic: AtomicFnPtr<Option<fn(i32) -> i32>> = AtomicFnPtr::new(None);
        *atomic.get_mut() = Some(double);
        assert_eq!(atomic.into_inner().unwrap()(4), 8);
    }

    #[test]
    fn option_compare_exchange_success() {
        let atomic: AtomicFnPtr<Option<fn(i32) -> i32>> = AtomicFnPtr::new(None);
        let result =
            atomic.compare_exchange(None, Some(add_one), Ordering::SeqCst, Ordering::SeqCst);
        assert!(result.is_ok());
        assert!(result.unwrap().is_none());
        assert_eq!(atomic.load(Ordering::SeqCst).unwrap()(7), 8);
    }

    #[test]
    fn option_compare_exchange_failure() {
        let atomic = AtomicFnPtr::new(Some(add_one as fn(i32) -> i32));
        let result =
            atomic.compare_exchange(None, Some(double), Ordering::SeqCst, Ordering::SeqCst);
        assert!(result.is_err());
        // Value unchanged
        assert_eq!(atomic.load(Ordering::SeqCst).unwrap()(5), 6);
    }
}
