#![no_std]

const PTR_SIZE: usize = core::mem::size_of::<*mut ()>();
const USIZE_SIZE: usize = core::mem::size_of::<usize>();

macro_rules! get_atomic {
    (($ty: ty, $u_cell: expr) => |$atomic: ident| { $($body:tt)* }) => {
        if core::mem::size_of::<$ty>() == PTR_SIZE {
            use core::sync::atomic::AtomicPtr;

            let $atomic = &*($u_cell.get() as *mut AtomicPtr<()>);
            $($body)*

        } else if core::mem::size_of::<$ty>() == USIZE_SIZE {
            use core::sync::atomic::AtomicUsize;

            let $atomic = &*($u_cell.get() as *mut AtomicUsize);
            $($body)*
        } else {
            use core::sync::atomic::{
                AtomicU8,
                AtomicU16,
                AtomicU32,
                AtomicU64,
            };

            match core::mem::size_of::<$ty>() {
                8 => {
                    let $atomic = &*($u_cell.get() as *mut AtomicU8);
                    $($body)*
                },
                16 => {
                    let $atomic = &*($u_cell.get() as *mut AtomicU16);
                    $($body)*
                },
                32 => {
                    let $atomic = &*($u_cell.get() as *mut AtomicU32);
                    $($body)*
                },
                64 => {
                    let $atomic = &*($u_cell.get() as *mut AtomicU64);
                    $($body)*
                },
                _ => panic!("The crate does not support the current platform"),
            }
        }
    }
}
use core::cell::UnsafeCell;
use core::fmt::{self, Formatter, Debug, Pointer};
use core::hash::Hash;
use core::panic::RefUnwindSafe;
use core::sync::atomic::Ordering;

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
    cell: UnsafeCell<T>,
}

impl<T: FnPtr> AtomicFnPtr<T> {
    /// Creates a new `AtomicFnPtr`.
    #[inline]
    pub fn new(fn_ptr: T) -> AtomicFnPtr<T> {
        AtomicFnPtr {
            cell: UnsafeCell::new(fn_ptr),
        }
    }

    /// Consumes the atomic and returns the contained value.
    ///
    /// This is safe because passing `self` by value guarantees that no other threads are
    /// concurrently accessing the atomic data.
    #[inline]
    pub fn into_inner(self) -> T {
        self.cell.into_inner()
    }

    /// Returns a mutable reference to the underlying pointer.
    ///
    /// This is safe because the mutable reference guarantees that no other threads are
    /// concurrently accessing the atomic data.
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        self.cell.get_mut()
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
    pub fn load(&self, order: Ordering) -> T {
        unsafe {
            get_atomic!((T, self.cell) => |atomic| {
                let raw = atomic.load(order);
                *((&raw) as *const _ as *const T)
            })
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
    pub fn store(&self, fn_ptr: T, order: Ordering) {
        unsafe {
            get_atomic!((T, self.cell) => |atomic| {
                atomic.store(*((&fn_ptr) as *const T as *const _), order);
            })
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
    pub fn swap(&self, fn_ptr: T, order: Ordering) -> T {
        unsafe {
            get_atomic!((T, self.cell) => |atomic| {
                let old_raw = atomic.swap(*((&fn_ptr) as *const T as *const _), order);
                *((&old_raw) as *const _ as *const T)
            })
        }
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
    /// operations on pointers.
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
    /// fn a_fn() {
    ///     println!("Called `a_fn`")
    /// }
    ///
    /// fn another_fn() {
    ///     println!("Called `another_fn`")
    /// }
    ///
    /// let ptr = a_fn;
    /// let some_ptr = AtomicFnPtr::new(ptr);
    /// let other_ptr = another_fn;
    ///
    /// (some_ptr.load(Ordering::SeqCst))();
    ///
    /// let value = some_ptr.compare_and_swap(ptr, other_ptr, Ordering::Relaxed);
    ///
    /// (some_ptr.load(Ordering::SeqCst))();
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
        unsafe {
            get_atomic!((T, self.cell) => |atomic| {
                let old_raw = atomic.compare_and_swap(
                    *((&current) as *const T as *const _),
                    *((&new) as *const T as *const _),
                    order
                );
                *((&old_raw) as *const _ as *const T)
            })
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
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::atomic::Ordering;
    /// use atomic_fn::AtomicFnPtr;
    ///
    /// fn a_fn() {
    ///     println!("Called `a_fn`")
    /// }
    ///
    /// fn another_fn() {
    ///     println!("Called `another_fn`")
    /// }
    ///
    /// let ptr = a_fn;
    /// let some_ptr  = AtomicFnPtr::new(ptr);
    /// let other_ptr  = another_fn;
    ///
    /// (some_ptr.load(Ordering::SeqCst))();
    ///
    /// let value = some_ptr.compare_exchange(
    ///     ptr,
    ///     other_ptr,
    ///     Ordering::SeqCst,
    ///     Ordering::Relaxed
    /// );
    ///
    /// (some_ptr.load(Ordering::SeqCst))();
    /// ```
    pub fn compare_exchange(
        &self,
        current: T,
        new: T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<T, T> {
        unsafe {
            get_atomic!((T, self.cell) => |atomic| {
                let result = atomic.compare_exchange(
                    *((&current) as *const T as *const _),
                    *((&new) as *const T as *const _),
                    success,
                    failure,
                );
                match result {
                    Ok(raw) => Ok(*((&raw) as *const _ as *const T)),
                    Err(raw) => Err(*((&raw) as *const _ as *const T))
                }
            })
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
    /// fn a_fn() {
    ///     println!("Called `a_fn`")
    /// }
    ///
    /// fn another_fn() {
    ///     println!("Called `another_fn`")
    /// }
    ///
    /// let some_ptr = AtomicFnPtr::new(a_fn);
    /// let new = another_fn;
    /// let mut old = some_ptr.load(Ordering::Relaxed);
    ///
    /// old();
    ///
    /// loop {
    ///     match some_ptr.compare_exchange_weak(old, new, Ordering::SeqCst, Ordering::Relaxed) {
    ///         Ok(x) => {
    ///             x();
    ///             break;
    ///         }
    ///         Err(x) => {
    ///             x();
    ///             old = x
    ///         }
    ///     }
    /// }
    /// ```
    pub fn compare_exchange_weak(
        &self,
        current: T,
        new: T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<T, T> {
        unsafe {
            get_atomic!((T, self.cell) => |atomic| {
                let result = atomic.compare_exchange_weak(
                    *((&current) as *const T as *const _),
                    *((&new) as *const T as *const _),
                    success,
                    failure,
                );
                match result {
                    Ok(raw) => Ok(*((&raw) as *const _ as *const T)),
                    Err(raw) => Err(*((&raw) as *const _ as *const T))
                }
            })
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
    /// fn a_fn() {
    ///     println!("Called `a_fn`")
    /// }
    ///
    /// fn another_fn() {
    ///     println!("Called `another_fn`")
    /// }
    ///
    /// let ptr: fn() = a_fn;
    /// let some_ptr = AtomicFnPtr::new(ptr);
    /// let new: fn() = another_fn;
    ///
    /// assert_eq!(some_ptr.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |_| None), Err(ptr));
    /// (some_ptr.load(Ordering::SeqCst))();
    /// let result = some_ptr.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |x| {
    ///     if x == ptr {
    ///         Some(new)
    ///     } else {
    ///         None
    ///     }
    /// });
    /// assert_eq!(result, Ok(ptr));
    /// (some_ptr.load(Ordering::SeqCst))();
    /// assert_eq!(some_ptr.load(Ordering::SeqCst), new);
    /// (some_ptr.load(Ordering::SeqCst))();
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
        unsafe {
            get_atomic!((T, self.cell) => |atomic| {
                let result = atomic.fetch_update(set_order, fetch_order, move |raw| {
                    match func(*((&raw) as *const _ as *const T)) {
                        Some(fn_ptr) => *((&fn_ptr) as *const T as *const _),
                        None => None
                    }
                });
                match result {
                    Ok(raw) => Ok(*((&raw) as *const _ as *const T)),
                    Err(raw) => Err(*((&raw) as *const _ as *const T))
                }
            })
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
    use core::mem::{align_of as align, size_of as size};

    let [/* The crate does not support the target platform. */] = [
        ();
        !(size::<fn()>() == 8 || size::<fn()>() == 16 || size::<fn()>() == 32 || size::<fn()>() == 64) as usize
    ];

    let [/* The crate does not support the target platform. */] = [
        ();
        !(align::<fn()>() == 1  || align::<fn()>() == 2 || align::<fn()>() == 4 || align::<fn()>() == 8) as usize
    ];
};
