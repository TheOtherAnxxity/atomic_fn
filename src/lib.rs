#![no_std]

use core::hash::Hash;
use core::sync::atomic::{AtomicPtr, Ordering};
use core::fmt::{self, Debug, Pointer, Formatter};

/// A function pointer type which can be safely shared between threads.
///
/// This type has the same in-memory representation as a `fn()`.
///
/// **Note**: This type is only available on platforms that support atomic
/// loads and stores of pointers. Its size depends on the target pointer's size.
#[repr(transparent)]
pub struct AtomicFnPtr<T: FnPtr> {
    atomic: AtomicPtr<FnPtrTarget>,
    _marker: core::marker::PhantomData<T>,
}

impl<T: FnPtr> AtomicFnPtr<T> {
    /// Creates a new `AtomicFnPtr`.
    #[inline]
    pub fn new(fn_ptr: T) -> AtomicFnPtr<T> {
        AtomicFnPtr {
            atomic: AtomicPtr::new(unsafe { fn_ptr_to_raw_ptr(fn_ptr) }),
            _marker: core::marker::PhantomData,
        }
    }

    /// Returns a mutable reference to the underlying pointer.
    ///
    /// This is safe because the mutable reference guarantees that no other threads are
    /// concurrently accessing the atomic data.
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        unsafe { mut_raw_ptr_to_mut_fn_ptr(self.atomic.get_mut()) }
    }

    /// Consumes the atomic and returns the contained value.
    ///
    /// This is safe because passing `self` by value guarantees that no other threads are
    /// concurrently accessing the atomic data.
    #[inline]
    pub fn into_inner(self) -> T {
        unsafe { raw_ptr_to_fn_ptr(self.atomic.into_inner()) }
    }

    /// Loads a value from the pointer.
    ///
    /// `load` takes an [`Ordering`] argument which describes the memory ordering
    /// of this operation. Possible values are [`SeqCst`], [`Acquire`] and [`Relaxed`].
    ///
    /// # Panics
    ///
    /// Panics if `order` is [`Release`] or [`AcqRel`].
    #[inline]
    pub fn load(&self, order: Ordering) -> T {
        unsafe { raw_ptr_to_fn_ptr(self.atomic.load(order)) }
    }

    /// Stores a value into the pointer.
    ///
    /// `store` takes an [`Ordering`] argument which describes the memory ordering
    /// of this operation. Possible values are [`SeqCst`], [`Release`] and [`Relaxed`].
    ///
    /// # Panics
    ///
    /// Panics if `order` is [`Acquire`] or [`AcqRel`].
    #[inline]
    pub fn store(&self, fn_ptr: T, order: Ordering) {
        self.atomic.store(unsafe { fn_ptr_to_raw_ptr(fn_ptr) }, order);
    }

    /// Stores a value into the pointer, returning the previous value.
    ///
    /// `swap` takes an [`Ordering`] argument which describes the memory ordering
    /// of this operation. All ordering modes are possible. Note that using
    /// [`Acquire`] makes the store part of this operation [`Relaxed`], and
    /// using [`Release`] makes the load part [`Relaxed`].
    ///
    /// **Note:** This method is only available on platforms that support atomic
    /// operations on pointers.
    #[inline]
    pub fn swap(&self, fn_ptr: T, order: Ordering) -> T {
        unsafe { raw_ptr_to_fn_ptr(self.atomic.swap(fn_ptr_to_raw_ptr(fn_ptr), order)) }
    }

    /// Stores a value into the pointer if the current value is the same as the `current` value.
    ///
    /// The return value is always the previous value. If it is equal to `current`, then the value
    /// was updated.
    ///
    /// `compare_and_swap` also takes an [`Ordering`] argument which describes the memory
    /// ordering of this operation. Notice that even when using [`AcqRel`], the operation
    /// might fail and hence just perform an `Acquire` load, but not have `Release` semantics.
    /// Using [`Acquire`] makes the store part of this operation [`Relaxed`] if it
    /// happens, and using [`Release`] makes the load part [`Relaxed`].
    ///
    /// **Note:** This method is only available on platforms that support atomic
    /// operations on pointers.
    ///
    /// # Migrating to `compare_exchange` and `compare_exchange_weak`
    ///
    /// `compare_and_swap` is equivalent to `compare_exchange` with the following mapping for
    /// memory orderings:
    ///
    /// Original | Success | Failure
    /// -------- | ------- | -------
    /// Relaxed  | Relaxed | Relaxed
    /// Acquire  | Acquire | Acquire
    /// Release  | Release | Relaxed
    /// AcqRel   | AcqRel  | Acquire
    /// SeqCst   | SeqCst  | SeqCst
    ///
    /// `compare_exchange_weak` is allowed to fail spuriously even when the comparison succeeds,
    /// which allows the compiler to generate better assembly code when the compare and swap
    /// is used in a loop.
    #[deprecated(
        since = "0.1.0",
        note = "\
            Use `compare_exchange` or `compare_exchange_weak` instead. \
            Only exists for compatibility with applications that use `compare_and_swap` on the `core` atomic types\
        "
    )]
    #[inline]
    pub fn compare_and_swap(&self, current: T, new: T, order: Ordering) -> T {
        #[allow(deprecated)] unsafe {
            raw_ptr_to_fn_ptr(
                self.atomic.compare_and_swap(
                    fn_ptr_to_raw_ptr(current),
                    fn_ptr_to_raw_ptr(new),
                    order,
                )
            )
        }
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
    /// the comparison fails. Using [`Acquire`] as success ordering makes the store part
    /// of this operation [`Relaxed`], and using [`Release`] makes the successful load
    /// [`Relaxed`]. The failure ordering can only be [`SeqCst`], [`Acquire`] or [`Relaxed`]
    /// and must be equivalent to or weaker than the success ordering.
    ///
    /// **Note:** This method is only available on platforms that support atomic
    /// operations on pointers.
    #[inline]
    pub fn compare_exchange(
        &self,
        current: T,
        new: T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<T, T> {
        unsafe {
            self.atomic
                .compare_exchange(
                    fn_ptr_to_raw_ptr(current),
                    fn_ptr_to_raw_ptr(new),
                    success,
                    failure,
                )
                .map(|ptr| raw_ptr_to_fn_ptr(ptr))
                .map_err(|ptr| raw_ptr_to_fn_ptr(ptr))
        }
    }

    /// Stores a value into the pointer if the current value is the same as the `current` value.
    ///
    /// Unlike [`AtomicPtr::compare_exchange`], this function is allowed to spuriously fail even when the
    /// comparison succeeds, which can result in more efficient code on some platforms. The
    /// return value is a result indicating whether the new value was written and containing the
    /// previous value.
    ///
    /// `compare_exchange_weak` takes two [`Ordering`] arguments to describe the memory
    /// ordering of this operation. `success` describes the required ordering for the
    /// read-modify-write operation that takes place if the comparison with `current` succeeds.
    /// `failure` describes the required ordering for the load operation that takes place when
    /// the comparison fails. Using [`Acquire`] as success ordering makes the store part
    /// of this operation [`Relaxed`], and using [`Release`] makes the successful load
    /// [`Relaxed`]. The failure ordering can only be [`SeqCst`], [`Acquire`] or [`Relaxed`]
    /// and must be equivalent to or weaker than the success ordering.
    ///
    /// **Note:** This method is only available on platforms that support atomic
    /// operations on pointers.
    #[inline]
    pub fn compare_exchange_weak(
        &self,
        current: T,
        new: T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<T, T> {
        unsafe {
            self.atomic
                .compare_exchange_weak(
                    fn_ptr_to_raw_ptr(current),
                    fn_ptr_to_raw_ptr(new),
                    success,
                    failure,
                )
                .map(|ptr| raw_ptr_to_fn_ptr(ptr))
                .map_err(|ptr| raw_ptr_to_fn_ptr(ptr))
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
    /// orderings of [`AtomicPtr::compare_exchange`] respectively.
    ///
    /// Using [`Acquire`] as success ordering makes the store part of this
    /// operation [`Relaxed`], and using [`Release`] makes the final successful
    /// load [`Relaxed`]. The (failed) load ordering can only be [`SeqCst`],
    /// [`Acquire`] or [`Relaxed`] and must be equivalent to or weaker than the
    /// success ordering.
    ///
    /// **Note:** This method is only available on platforms that support atomic
    /// operations on pointers.
    #[inline]
    pub fn fetch_update<F>(
        &self,
        set_order: Ordering,
        fetch_order: Ordering,
        mut func: F,
    ) -> Result<T, T>
        where
            F: FnMut(T) -> Option<T>,
    {
        unsafe {
            let func = move |ptr: *mut FnPtrTarget|
                func(raw_ptr_to_fn_ptr(ptr)).map(|ptr| fn_ptr_to_raw_ptr(ptr));

            self.atomic
                .fetch_update(
                    set_order,
                    fetch_order,
                    func,
                )
                .map(|ptr| raw_ptr_to_fn_ptr(ptr))
                .map_err(|ptr| raw_ptr_to_fn_ptr(ptr))
        }
    }
}

impl<T: FnPtr> From<T> for AtomicFnPtr<T> {
    #[inline]
    fn from(fn_ptr: T) -> AtomicFnPtr<T> {
        AtomicFnPtr::new(fn_ptr)
    }
}

impl<T: FnPtr> Debug for AtomicFnPtr<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // This is the same inner code as AtomicPtr::fmt
        // This is only done this way in case the formatting of function pointers and data pointers diverges
        Debug::fmt(&self.load(Ordering::SeqCst), f)
    }
}

impl<T: FnPtr> Pointer for AtomicFnPtr<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // This is the same inner code as AtomicPtr::fmt
        // This is only done this way in case the formatting of function pointers and data pointers diverges
        Pointer::fmt(&self.load(Ordering::SeqCst), f)
    }
}

unsafe fn fn_ptr_to_raw_ptr<T: FnPtr>(fn_ptr: T) -> *mut FnPtrTarget {
    *((&fn_ptr) as *const T as *const *mut FnPtrTarget)
}

unsafe fn raw_ptr_to_fn_ptr<T: FnPtr>(raw_ptr: *mut FnPtrTarget) -> T {
    *((&raw_ptr) as *const *mut FnPtrTarget as *const T)
}

unsafe fn mut_raw_ptr_to_mut_fn_ptr<T: FnPtr>(raw_ptr: &mut *mut FnPtrTarget) -> &mut T {
    &mut *(raw_ptr as *mut *mut FnPtrTarget as *mut T)
}

mod sealed {
    pub trait FnPtrSealed {}
}

pub trait FnPtr: Copy + Eq + Ord + Hash + Pointer + Debug + sealed::FnPtrSealed {
    // Empty
}

#[repr(i8)]
#[allow(dead_code)]
enum FnPtrTarget {
    Variant1,
    Variant2,
}

macro_rules! impl_fn_ptr {
    ($($arg:ident),+) => {
        impl<Ret, $($arg),+> sealed::FnPtrSealed for fn($($arg),+) -> Ret {}
        impl<Ret, $($arg),+> FnPtr for fn($($arg),+) -> Ret {}
        impl<Ret, $($arg),+> sealed::FnPtrSealed for unsafe fn($($arg),+) -> Ret {}
        impl<Ret, $($arg),+> FnPtr for unsafe fn($($arg),+) -> Ret {}
        impl<Ret, $($arg),+> sealed::FnPtrSealed for extern "C" fn($($arg),+) -> Ret {}
        impl<Ret, $($arg),+> FnPtr for extern "C" fn($($arg),+) -> Ret {}
        impl<Ret, $($arg),+> sealed::FnPtrSealed for unsafe extern "C" fn($($arg),+) -> Ret {}
        impl<Ret, $($arg),+> FnPtr for unsafe extern "C" fn($($arg),+) -> Ret {}
        impl<Ret, $($arg),+> sealed::FnPtrSealed for extern "C" fn($($arg),+ , ...) -> Ret {}
        impl<Ret, $($arg),+> FnPtr for extern "C" fn($($arg),+ , ...) -> Ret {}
        impl<Ret, $($arg),+> sealed::FnPtrSealed for unsafe extern "C" fn($($arg),+ , ...) -> Ret {}
        impl<Ret, $($arg),+> FnPtr for unsafe extern "C" fn($($arg),+ , ...) -> Ret {}
    };
    // Variadic functions must have at least one non variadic arg
    () => {
        impl<Ret> sealed::FnPtrSealed for fn() -> Ret {}
        impl<Ret> FnPtr for fn() -> Ret {}
        impl<Ret> sealed::FnPtrSealed for unsafe fn() -> Ret {}
        impl<Ret> FnPtr for unsafe fn() -> Ret {}
        impl<Ret> sealed::FnPtrSealed for extern "C" fn() -> Ret {}
        impl<Ret> FnPtr for extern "C" fn() -> Ret {}
        impl<Ret> sealed::FnPtrSealed for unsafe extern "C" fn() -> Ret {}
        impl<Ret> FnPtr for unsafe extern "C" fn() -> Ret {}
    };
}

impl_fn_ptr!();
impl_fn_ptr!(A, B);
impl_fn_ptr!(A, B, C);
impl_fn_ptr!(A, B, C, D);
impl_fn_ptr!(A, B, C, D, E);
impl_fn_ptr!(A, B, C, D, E, F);
impl_fn_ptr!(A, B, C, D, E, F, G);
impl_fn_ptr!(A, B, C, D, E, F, G, H);
impl_fn_ptr!(A, B, C, D, E, F, G, H, I);
impl_fn_ptr!(A, B, C, D, E, F, G, H, I, J);
impl_fn_ptr!(A, B, C, D, E, F, G, H, I, J, K);
impl_fn_ptr!(A, B, C, D, E, F, G, H, I, J, K, L);
//impl_fn_ptr!(A, B, C, D, E, F, G, H, I, J, K, L, M);
//impl_fn_ptr!(A, B, C, D, E, F, G, H, I, J, K, L, M, N);
//impl_fn_ptr!(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O);
//impl_fn_ptr!(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P);

const  _: () = {
    use core::mem::{size_of, align_of};
    let [] = [(); align_of::<fn()>() - align_of::<*mut FnPtrTarget>()];
    let [] = [(); size_of::<fn()>() - size_of::<*mut FnPtrTarget>()];
    //if size_of::<fn()>() != size_of::<*mut FnPtrTarget>() || align_of::<fn()>() != align_of::<*mut FnPtrTarget>() {
    //    panic!("The layout of function pointers and data pointers may not be the same on the target platform.")
    //}
};
