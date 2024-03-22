#![no_std]

use core::cell::UnsafeCell;
use core::hash::Hash; //
use core::sync::atomic::{AtomicPtr, Ordering}; //
use core::fmt::{self, Debug, Pointer, Formatter};
use core::panic::RefUnwindSafe;
use core::sync::atomic; //

/// A function pointer type which can be safely shared between threads.
///
/// This type has the same in-memory representation as a `fn()`.
///
/// **Note**: This type is only available on platforms that support atomic
/// loads and stores of pointers. Its size depends on the target's pointer size.
#[cfg_attr(target_pointer_width = "8", repr(C, align(1)))]
#[cfg_attr(target_pointer_width = "16", repr(C, align(2)))]
#[cfg_attr(target_pointer_width = "32", repr(C, align(4)))]
#[cfg_attr(target_pointer_width = "64", repr(C, align(8)))]
pub struct AtomicFnPtr<T: FnPtr> {
    cell: UnsafeCell<T>
}

impl<T: FnPtr> AtomicFnPtr<T> {
    /// Creates a new `AtomicFnPtr`.
    #[inline]
    pub fn new(fn_ptr: T) -> AtomicFnPtr<T> {
        AtomicFnPtr {
            cell: UnsafeCell::new(fn_ptr)
        }
    }

    /// Returns a mutable reference to the underlying pointer.
    ///
    /// This is safe because the mutable reference guarantees that no other threads are
    /// concurrently accessing the atomic data.
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        self.cell.get_mut()
    }

    /// Consumes the atomic and returns the contained value.
    ///
    /// This is safe because passing `self` by value guarantees that no other threads are
    /// concurrently accessing the atomic data.
    #[inline]
    pub fn into_inner(self) -> T {
        self.cell.into_inner()
    }

    /// Loads a value from the pointer.
    ///
    /// `load` takes an [`Ordering`] argument which describes the memory ordering
    /// of this operation. Possible values are [`Ordering::SeqCst`], [`Ordering::Acquire`] and [`Ordering::Relaxed`].
    ///
    /// # Panics
    ///
    /// Panics if `order` is [`Ordering::Release`] or [`Ordering::AcqRel`].
    #[inline]
    pub fn load(&self, order: Ordering) -> T {
        unsafe {
            let atomic = &*(self.cell.get() as *mut AtomicPtr<()>);
            let raw_ptr = atomic.load(order);
            *((&raw_ptr) as *const *mut () as *const T)
        }
    }

    /// Stores a value into the pointer.
    ///
    /// `store` takes an [`Ordering`] argument which describes the memory ordering
    /// of this operation. Possible values are [`Ordering::SeqCst`], [`Ordering::Release`] and [`Ordering::Relaxed`].
    ///
    /// # Panics
    ///
    /// Panics if `order` is [`Ordering::Acquire`] or [`Ordering::AcqRel`].
    #[inline]
    pub fn store(&self, fn_ptr: T, order: Ordering) {
        unsafe {
            let atomic = &*(self.cell.get() as *mut AtomicPtr<()>);
            let raw_ptr = *((&fn_ptr) as *const T as *const *mut ());
            atomic.store(raw_ptr, order);
        }
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
    #[inline]
    pub fn swap(&self, fn_ptr: T, order: Ordering) -> T {
        unsafe {
            let atomic = &*(self.cell.get() as *mut AtomicPtr<()>);
            let new_raw_ptr = *((&fn_ptr) as *const T as *const *mut ());
            let old_raw_ptr = atomic.swap(new_raw_ptr, order);
            *((&old_raw_ptr) as *const *mut () as *const T)
        }
    }

    /// Stores a value into the pointer if the current value is the same as the `current` value.
    ///
    /// The return value is always the previous value. If it is equal to `current`, then the value
    /// was updated.
    ///
    /// `compare_and_swap` also takes an [`Ordering`] argument which describes the memory
    /// ordering of this operation. Notice that even when using [`Ordering::AcqRel`], the operation
    /// might fail and hence just perform an `Ordering::Acquire` load, but not have `Ordering::Release` semantics.
    /// Using [`Ordering::Acquire`] makes the store part of this operation [`Ordering::Relaxed`] if it
    /// happens, and using [`Ordering::Release`] makes the load part [`Ordering::Relaxed`].
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
    /// Ordering::Relaxed  | Ordering::Relaxed | Ordering::Relaxed
    /// Ordering::Acquire  | Ordering::Acquire | Ordering::Acquire
    /// Ordering::Release  | Ordering::Release | Ordering::Relaxed
    /// Ordering::AcqRel   | Ordering::AcqRel  | Ordering::Acquire
    /// Ordering::SeqCst   | Ordering::SeqCst  | Ordering::SeqCst
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
        #[allow(deprecated)]
        unsafe {
            let atomic = &*(self.cell.get() as *mut AtomicPtr<()>);
            let current_raw = *((&current) as *const T as *const *mut ());
            let new_raw = *((&new) as *const T as *const *mut ());
            let old_raw = atomic.compare_and_swap(current_raw, new_raw, order);
            *((&old_raw) as *const *mut () as *const T)
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
    /// the comparison fails. Using [`Ordering::Acquire`] as success ordering makes the store part
    /// of this operation [`Ordering::Relaxed`], and using [`Ordering::Release`] makes the successful load
    /// [`Ordering::Relaxed`]. The failure ordering can only be [`Ordering::SeqCst`], [`Ordering::Acquire`] or [`Ordering::Relaxed`]
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
            let atomic = &*(self.cell.get() as *mut AtomicPtr<()>);
            let current_raw = *((&current) as *const T as *const *mut ());
            let new_raw = *((&new) as *const T as *const *mut ());
            atomic
                .compare_exchange(
                    current_raw,
                    new_raw,
                    success,
                    failure
                )
                .map(|raw_ptr| *((&raw_ptr) as *const *mut () as *const T))
                .map_err(|raw_ptr| *((&raw_ptr) as *const *mut () as *const T))
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
    /// the comparison fails. Using [`Ordering::Acquire`] as success ordering makes the store part
    /// of this operation [`Ordering::Relaxed`], and using [`Ordering::Release`] makes the successful load
    /// [`Ordering::Relaxed`]. The failure ordering can only be [`Ordering::SeqCst`], [`Ordering::Acquire`] or [`Ordering::Relaxed`]
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
            let atomic = &*(self.cell.get() as *mut AtomicPtr<()>);
            let current_raw = *((&current) as *const T as *const *mut ());
            let new_raw = *((&new) as *const T as *const *mut ());
            atomic
                .compare_exchange_weak(
                    current_raw,
                    new_raw,
                    success,
                    failure
                )
                .map(|raw_ptr| *((&raw_ptr) as *const *mut () as *const T))
                .map_err(|raw_ptr| *((&raw_ptr) as *const *mut () as *const T))
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
    /// Using [`Ordering::Acquire`] as success ordering makes the store part of this
    /// operation [`Ordering::Relaxed`], and using [`Ordering::Release`] makes the final successful
    /// load [`Ordering::Relaxed`]. The (failed) load ordering can only be [`Ordering::SeqCst`],
    /// [`Ordering::Acquire`] or [`Ordering::Relaxed`] and must be equivalent to or weaker than the
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
            let atomic = &*(self.cell.get() as *mut AtomicPtr<()>);
            let func = move |raw_ptr: *mut ()| {
                let old_fn_ptr = *((&raw_ptr) as *const *mut () as *const T);
                func(old_fn_ptr).map(|fn_ptr| *((&fn_ptr) as *const T as *const *mut ()))
            };
            atomic
                .fetch_update(set_order, fetch_order, func)
                .map(|raw_ptr| *((&raw_ptr) as *const *mut () as *const T))
                .map_err(|raw_ptr| *((&raw_ptr) as *const *mut () as *const T))
        }
    }
}

// SAFETY: We only access the memory atomically
unsafe impl<T: FnPtr> Sync for AtomicFnPtr<T> {}

// SAFETY: We only access the memory atomically
impl<T: FnPtr> RefUnwindSafe for AtomicFnPtr<T> {}

impl<T: FnPtr> From<T> for AtomicFnPtr<T> {
    #[inline]
    fn from(fn_ptr: T) -> AtomicFnPtr<T> {
        AtomicFnPtr::new(fn_ptr)
    }
}

impl<T: FnPtr> Debug for AtomicFnPtr<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // This is the same inner code as AtomicPtr::fmt
        // This is only done this way in case
        // the formatting of function pointers and data pointers diverges
        Debug::fmt(&self.load(Ordering::SeqCst), f)
    }
}

impl<T: FnPtr> Pointer for AtomicFnPtr<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // This is the same inner code as AtomicPtr::fmt
        // This is only done this way in case
        // the formatting of function pointers and data pointers diverges
        Pointer::fmt(&self.load(Ordering::SeqCst), f)
    }
}

mod sealed {
    pub trait FnPtrSealed {}
}

pub trait FnPtr: Copy + Eq + Ord + Hash + Pointer + Debug + sealed::FnPtrSealed {
    // Empty
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

const _: () = {
    use core::mem::{size_of, align_of};
    // If the align of both is equal, we get false, which is 0 when cast to an unsigned type
    let [] = ["The layout of function pointers and data pointers is not be the same on the target platform.";
        (align_of::<fn()>() != align_of::<*mut FnPtrTarget>()) as usize
    ];
    // If the size of both is equal, we get false, which is 0 when cast to an unsigned type
    let [] = ["The layout of function pointers and data pointers is not be the same on the target platform.";
        (size_of::<fn()>() != size_of::<*mut FnPtrTarget>()) as usize
    ];
    /*
    if size_of::<fn()>() != size_of::<*mut FnPtrTarget>() || align_of::<fn()>() != align_of::<*mut FnPtrTarget>() {
        panic!("The layout of function pointers and data pointers is not be the same on the target platform.")
    }
    */
};
