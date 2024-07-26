#![no_std]

//! A small, no_std crate that adds atomic function pointers.
//! See [`AtomicFnPtr`] for examples.

use core::fmt::{self, Formatter, Debug, Pointer};
use core::marker::PhantomData;
use core::sync::atomic::{AtomicPtr, Ordering};

/// An atomically mutable function pointer type which can be safely shared between threads.
pub struct AtomicFnPtr<T: FnPtr> {
    atomic: AtomicPtr<()>,
    phantom: PhantomData<T>,
}

impl<T: FnPtr> AtomicFnPtr<T> {
    /// Creates a new [`AtomicFnPtr`].
    /// 
    /// Note that in some cases you may gave to cast/coerce the `fn_pointer` to its type, since Rust's type system
    /// otherwise assigns a custom type signature to each named function and anonymous closure. See the related 
    /// examples. If you run into this issue, it will be at compile time.
    /// 
    /// # Examples 
    /// 
    /// Constructing an [`AtomicFnPtr`] from a named function without casting fails to compile.
    /// ```compile_fail
    /// use std::sync::atomic::Ordering;
    /// use atomic_fn::AtomicFnPtr;
    /// 
    /// fn fn_a() {
    ///     println!("Hello from fn_a");
    /// }
    /// 
    /// let atomic_ptr = AtomicFnPtr::new(fn_a);
    /// ```
    /// 
    /// Constructing an [`AtomicFnPtr`] from a named function with a cast succeeds.
    /// ```rust
    /// use std::sync::atomic::Ordering;
    /// use atomic_fn::AtomicFnPtr;
    /// 
    /// fn fn_a() {
    ///     println!("Hello from fn_a");
    /// }
    /// 
    /// let atomic_ptr = AtomicFnPtr::new(fn_a as fn() -> ());
    /// ```
    /// 
    /// Constructing an [`AtomicFnPtr`] from an anonymous closure without type coercion fails to compile.
    /// 
    /// ```compile_fail
    /// use std::sync::atomic::Ordering;
    /// use atomic_fn::AtomicFnPtr;
    /// 
    /// let fn_a = || {
    ///     println!("Hello from fn_a");
    /// };
    /// 
    /// let atomic_ptr = AtomicFnPtr::new(fn_a);
    /// ```
    /// 
    /// Constructing an [`AtomicFnPtr`] from an anonymous closure with type coercion succeeds.
    /// 
    /// ```rust
    /// use std::sync::atomic::Ordering;
    /// use atomic_fn::AtomicFnPtr;
    /// 
    /// let fn_a: fn() -> () = || {
    ///     println!("Hello from fn_a");
    /// };
    /// 
    /// let atomic_ptr = AtomicFnPtr::new(fn_a);
    /// ```
    /// 
    #[inline]
    pub fn new(fn_ptr: T) -> AtomicFnPtr<T> {
        AtomicFnPtr {
            atomic: AtomicPtr::new(fn_ptr.as_void_ptr()),
            phantom: PhantomData
        }
    }

    /// Consumes the atomic and returns the contained value.
    ///
    /// This is safe because passing `self` by value guarantees that no other threads are
    /// concurrently accessing the atomic data.
    #[inline]
    pub fn into_inner(self) -> T
    {
        let void_ptr: *mut () = self.atomic.into_inner();

        // SAFETY: Transmutation from a raw pointer into a function pointer is one of the recommended use-cases
        // and in this case is sound because AtomicFnPtr cannot be constructed without passing in a function pointer 
        // of type T -- thus transmuting back to T is fine here.
        unsafe {
            T::transmute_from_void(void_ptr)
        }
    }

    /// Returns a mutable reference to the underlying pointer.
    ///
    /// This is safe because the mutable reference guarantees that no other threads are
    /// concurrently accessing the atomic data.
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        let mut_ref_to_void_ptr = self.atomic.get_mut();

        // SAFETY: 
        // The void pointer to function pointer transmution we do here is safe for the same reasons as the one 
        // above.
        unsafe {
            core::mem::transmute(mut_ref_to_void_ptr)
        }
    }
}

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
        let void_ptr: *mut () = self.atomic.load(order);

        // SAFETY: This is safe for the same reasons as above.
        unsafe {
            T::transmute_from_void(void_ptr)
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
        self.atomic.store(fn_ptr.as_void_ptr(), order)
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
        let void_ptr = self.atomic.swap(fn_ptr.as_void_ptr(), order);

        // SAFETY: This is safe for the same reasons as above.
        unsafe {
            T::transmute_from_void(void_ptr)
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
    /// let some_ptr  = AtomicFnPtr::new(ptr as fn() -> ());
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
        let result: Result<_, _> = self.atomic
            .compare_exchange(current.as_void_ptr(), new.as_void_ptr(), success, failure);

        // SAFETY: Safe for the same reasons as above.
        match result {
            Ok(void_ptr) => Ok(unsafe { T::transmute_from_void(void_ptr) }),
            Err(void_ptr) => Err(unsafe { T::transmute_from_void(void_ptr) })
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
    /// let some_ptr = AtomicFnPtr::new(a_fn as fn() -> ());
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
        let result: Result<_, _> = self.atomic
            .compare_exchange_weak(current.as_void_ptr(), new.as_void_ptr(), success, failure);
        
        // SAFETY: Safe for the same reasons as above.
        match result {
            Ok(void_ptr) => Ok(unsafe { T::transmute_from_void(void_ptr) }),
            Err(void_ptr) => Err(unsafe { T::transmute_from_void(void_ptr) })
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
        let result: Result<_, _> = self.atomic.fetch_update(set_order, fetch_order, move |void_ptr: *mut ()| {
            // SAFETY: Safe for the same reasons as above.
            let fn_ptr = unsafe { T::transmute_from_void(void_ptr) };
            let func_output = (func)(fn_ptr);
            func_output.map(T::as_void_ptr)
        });

        // SAFETY: Safe for the same reasons as above.
        match result {
            Ok(void_ptr) => Ok(unsafe { T::transmute_from_void(void_ptr) }),
            Err(void_ptr) => Err(unsafe { T::transmute_from_void(void_ptr) })
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
        Debug::fmt(&self.load(Ordering::Relaxed), f)
    }
}

impl<T: FnPtr + Pointer> Pointer for AtomicFnPtr<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // This is the same inner code as AtomicPtr::fmt
        // This is only done this way in case
        // the formatting of function pointers and data pointers diverges
        Pointer::fmt(&self.load(Ordering::Relaxed), f)
    }
}

// // SAFETY: We only access the memory atomically
// unsafe impl<T: FnPtr + Sync> Sync for AtomicFnPtr<T> {}

// // SAFETY: We only access the memory atomically
// impl<T: FnPtr + RefUnwindSafe> RefUnwindSafe for AtomicFnPtr<T> {}

mod sealed {
    pub trait FnPtrSealed: Copy {}
}

pub trait FnPtr: Copy + sealed::FnPtrSealed /* Eq + Ord + Hash + Pointer + Debug */ {
    /// Cast this function pointer to a `*mut ()` using a simple `as *mut ()` cast.
    fn as_void_ptr(self) -> *mut ();

    /// Call [core::mem::transmute] from the given void pointer to this type.
    /// This will give a compiler error (E0512) if this type is not pointer sized (should never happen 
    /// given that this trait is sealed). 
    /// 
    /// # Safety
    /// This is unsafe for the same reasons as [core::mem::transmute].
    unsafe fn transmute_from_void(void_ptr: *mut ()) -> Self;
}

macro_rules! impl_fn_ptr {
    ($($arg:ident),+) => {
        impl<Ret, $($arg),+> sealed::FnPtrSealed for fn($($arg),+) -> Ret {}
        impl<Ret, $($arg),+> FnPtr for fn($($arg),+) -> Ret { 
            fn as_void_ptr(self) -> *mut () {
                self as *mut ()
            }

            unsafe fn transmute_from_void(void_ptr: *mut ()) -> Self {
                core::mem::transmute(void_ptr)
            }
        }

        impl<Ret, $($arg),+> sealed::FnPtrSealed for unsafe fn($($arg),+) -> Ret {}
        impl<Ret, $($arg),+> FnPtr for unsafe fn($($arg),+) -> Ret {
            fn as_void_ptr(self) -> *mut () {
                self as *mut ()
            }
            
            unsafe fn transmute_from_void(void_ptr: *mut ()) -> Self {
                core::mem::transmute(void_ptr)
            }
        }

        impl<Ret, $($arg),+> sealed::FnPtrSealed for extern "C" fn($($arg),+) -> Ret {}
        impl<Ret, $($arg),+> FnPtr for extern "C" fn($($arg),+) -> Ret {
            fn as_void_ptr(self) -> *mut () {
                self as *mut ()
            }
            
            unsafe fn transmute_from_void(void_ptr: *mut ()) -> Self {
                core::mem::transmute(void_ptr)
            }
        }
        
        impl<Ret, $($arg),+> sealed::FnPtrSealed for unsafe extern "C" fn($($arg),+) -> Ret {}
        impl<Ret, $($arg),+> FnPtr for unsafe extern "C" fn($($arg),+) -> Ret {
            fn as_void_ptr(self) -> *mut () {
                self as *mut ()
            }
            
            unsafe fn transmute_from_void(void_ptr: *mut ()) -> Self {
                core::mem::transmute(void_ptr)
            }
        }
        
        impl<Ret, $($arg),+> sealed::FnPtrSealed for extern "C" fn($($arg),+ , ...) -> Ret {}
        impl<Ret, $($arg),+> FnPtr for extern "C" fn($($arg),+ , ...) -> Ret {
            fn as_void_ptr(self) -> *mut () {
                self as *mut ()
            }
            
            unsafe fn transmute_from_void(void_ptr: *mut ()) -> Self {
                core::mem::transmute(void_ptr)
            }
        }

        impl<Ret, $($arg),+> sealed::FnPtrSealed for unsafe extern "C" fn($($arg),+ , ...) -> Ret {}
        impl<Ret, $($arg),+> FnPtr for unsafe extern "C" fn($($arg),+ , ...) -> Ret {
            fn as_void_ptr(self) -> *mut () {
                self as *mut ()
            }
            
            unsafe fn transmute_from_void(void_ptr: *mut ()) -> Self {
                core::mem::transmute(void_ptr)
            }
        }
    };

    // Variadic functions must have at least one non variadic arg
    () => {
        impl<Ret> sealed::FnPtrSealed for fn() -> Ret {}
        impl<Ret> FnPtr for fn() -> Ret {
            fn as_void_ptr(self) -> *mut () {
                self as *mut ()
            }
            
            unsafe fn transmute_from_void(void_ptr: *mut ()) -> Self {
                core::mem::transmute(void_ptr)
            }
        }

        impl<Ret> sealed::FnPtrSealed for unsafe fn() -> Ret {}
        impl<Ret> FnPtr for unsafe fn() -> Ret {
            fn as_void_ptr(self) -> *mut () {
                self as *mut ()
            }
            
            unsafe fn transmute_from_void(void_ptr: *mut ()) -> Self {
                core::mem::transmute(void_ptr)
            }
        }

        impl<Ret> sealed::FnPtrSealed for extern "C" fn() -> Ret {}
        impl<Ret> FnPtr for extern "C" fn() -> Ret {
            fn as_void_ptr(self) -> *mut () {
                self as *mut ()
            }
            
            unsafe fn transmute_from_void(void_ptr: *mut ()) -> Self {
                core::mem::transmute(void_ptr)
            }
        }

        impl<Ret> sealed::FnPtrSealed for unsafe extern "C" fn() -> Ret {}
        impl<Ret> FnPtr for unsafe extern "C" fn() -> Ret {
            fn as_void_ptr(self) -> *mut () {
                self as *mut ()
            }
            
            unsafe fn transmute_from_void(void_ptr: *mut ()) -> Self {
                core::mem::transmute(void_ptr)
            }
        }
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
impl_fn_ptr!(A, B, C, D, E, F, G, H, I, J, K, L, M);
impl_fn_ptr!(A, B, C, D, E, F, G, H, I, J, K, L, M, N);
impl_fn_ptr!(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O);
impl_fn_ptr!(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P);

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

#[cfg(test)]
mod tests {
    use core::sync::atomic::Ordering;

    use crate::AtomicFnPtr;

    #[test]
    fn test_load_store() {
        let a: fn() = || { panic!("panic from a") };
        let b: fn() = || { panic!("panic from b") };

        let atomic: AtomicFnPtr<fn()> = AtomicFnPtr::new(a);
        assert_eq!(atomic.load(Ordering::Relaxed), a);

        atomic.store(b, Ordering::Relaxed);
        assert_eq!(atomic.load(Ordering::Relaxed), b);
    }
}
