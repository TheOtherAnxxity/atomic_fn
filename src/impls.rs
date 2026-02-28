use crate::FnPtr;
use core::sync::atomic;

/// Ideally, an atomic pointer is used, with a function pointer being the
/// same size as a data pointer.
const USE_ATOMIC_PTR: bool =
    cfg!(target_has_atomic = "ptr") && size_of::<fn()>() == size_of::<*mut ()>();

/// Uses const generics to statically select an atomic and raw inner type that
/// is layout-compatible with a `fn()`.
///
/// # Safety
/// - The types in `Atomic` and `Raw` must have the same size as `SIZE`.
/// - If `USE_ATOMIC_PTR` is `true`, they must be `AtomicPtr<U>` and `*mut U`
///   respectively.
/// - These types must not have stricter bit validity requirements than `fn`.
pub unsafe trait SelectAtomicFnInner<const USE_ATOMIC_PTR: bool, const SIZE: usize> {
    /// The equivalent `Atomic` type with a size and alignment compatible
    /// with `fn` on this platform.
    type Atomic;

    /// The non-atomic type stored in the [`AtomicFnInner`] atomic type.
    type Raw;

    /// The value with which to represent a `None::<fn()>>`.
    const ZERO: Self::Raw;
}

#[cfg(target_has_atomic = "ptr")]
unsafe impl SelectAtomicFnInner<true, { size_of::<*mut ()>() }> for fn() {
    type Atomic = atomic::AtomicPtr<()>;
    type Raw = *mut ();
    const ZERO: Self::Raw = core::ptr::null_mut();
}

#[cfg(target_has_atomic = "16")]
unsafe impl SelectAtomicFnInner<false, { size_of::<u16>() }> for fn() {
    type Atomic = atomic::AtomicU16;
    type Raw = u16;
    const ZERO: Self::Raw = 0;
}

#[cfg(target_has_atomic = "32")]
unsafe impl SelectAtomicFnInner<false, { size_of::<u32>() }> for fn() {
    type Atomic = atomic::AtomicU32;
    type Raw = u32;
    const ZERO: Self::Raw = 0;
}

#[cfg(target_has_atomic = "64")]
unsafe impl SelectAtomicFnInner<false, { size_of::<u64>() }> for fn() {
    type Atomic = atomic::AtomicU64;
    type Raw = u64;
    const ZERO: Self::Raw = 0;
}

/// An `Atomic` type with a size and alignment compatible to store and load any
/// `fn` on this platform.
pub type AtomicFnInner =
    <fn() as SelectAtomicFnInner<USE_ATOMIC_PTR, { size_of::<fn()>() }>>::Atomic;

/// The non-atomic type stored in the [`AtomicFnInner`] atomic type.
pub type AtomicFnInnerRaw =
    <fn() as SelectAtomicFnInner<USE_ATOMIC_PTR, { size_of::<fn()>() }>>::Raw;

const _: () = assert!(
    size_of::<AtomicFnInner>() == size_of::<fn()>()
        && size_of::<AtomicFnInner>() == size_of::<AtomicFnInnerRaw>()
);
const _: fn(&AtomicFnInner) = |inner: &AtomicFnInner| {
    let _check_inner_type: *mut AtomicFnInnerRaw = inner.as_ptr();
};

/// # Safety
/// The value returned by `to_raw` must be valid to pass to `from_raw`.
pub unsafe trait FnPtrSealed: Copy {
    // These methods are inaccesible outside of the crate as they are
    // within a sealed trait.
    #[doc(hidden)]
    fn to_raw(self) -> AtomicFnInnerRaw;

    #[inline(always)]
    #[doc(hidden)]
    /// # Safety
    ///
    /// The bytes of `raw` must make up a valid instance of `Self`.
    unsafe fn from_raw(raw: AtomicFnInnerRaw) -> Self {
        // This should already be guaranteed by static type dispatch.
        const { assert!(size_of::<AtomicFnInnerRaw>() == size_of::<Self>()) }

        // Note: Integer-to-pointer transmutes (including through `union`)
        // are considered problematic. It is best to first cast to `*mut ()`
        // to ensure proper pointer provenance.
        // See https://doc.rust-lang.org/std/primitive.fn.html#casting-to-and-from-integers.
        // However, this recommendation can only be followed if a `*mut ()`
        // can be `transmute`d back into a `fn()` by having the same size.

        // SAFETY: The caller promised that `transmute` is valid, since
        //         the source and destination sizes are confirmed equal.
        unsafe { core::mem::transmute_copy(&raw) }
    }
}

unsafe impl<T: FnPtrSealed> FnPtrSealed for Option<T> {
    fn to_raw(self) -> AtomicFnInnerRaw {
        match self {
            Some(inner) => inner.to_raw(),
            None => <fn() as SelectAtomicFnInner<USE_ATOMIC_PTR, { size_of::<fn()>() }>>::ZERO,
        }
    }
}

impl<T: FnPtr> FnPtr for Option<T> {}

macro_rules! impl_fn_ptr {
    (@impl traits ($($generics:tt)*) $fn:ty) => {
        // SAFETY: the return of `to_raw` is a valid instance of `self`
        unsafe impl<Ret $($generics)*> FnPtrSealed for $fn {
            fn to_raw(self) -> AtomicFnInnerRaw {
                self as AtomicFnInnerRaw
            }
        }
        impl<Ret $($generics)*> FnPtr for $fn {}
    };
    (@impl plus_unsafe ($($generics:tt)*) ($($rest:tt)*)) => {
        impl_fn_ptr!(@impl traits ($($generics)*) $($rest)*);
        impl_fn_ptr!(@impl traits ($($generics)*) unsafe $($rest)*);
    };
    (@impl with_abi $generics:tt extern $abi:literal ($($rest:tt)*)) => {
        impl_fn_ptr!(@impl plus_unsafe $generics (extern $abi $($rest)*));
    };
    (@impl abis $generics:tt [$($abi:literal),* $(,)?] $rest:tt) => {
        $(impl_fn_ptr!(@impl with_abi $generics extern $abi $rest);)*
    };
    (@impl variadics $($arg:ident),+) => {
        impl_fn_ptr!(
            @impl abis ($(,$arg)+)
            ["C", "C-unwind", "system", "system-unwind"]
            (fn($($arg),+ , ...) -> Ret)
        );
    };
    (@impl variadics) => {
        // Variadic functions must have at least one non variadic arg
    };
    ($($arg:ident),*) => {
        impl_fn_ptr!(@impl plus_unsafe ($(,$arg)*) (fn($($arg),*) -> Ret));
        impl_fn_ptr!(
            @impl abis ($(,$arg)*)
            ["C", "C-unwind", "system", "system-unwind"]
            (fn($($arg),*) -> Ret)
        );
        // TODO: support platform-specific ABIs
        impl_fn_ptr!(@impl variadics $($arg),*);
    };
}

const _: fn() = || {
    fn check_impl<T: FnPtr>() {}
    check_impl::<fn(i32)>();
    check_impl::<unsafe fn(*mut ()) -> &'static u32>();
    check_impl::<unsafe extern "C-unwind" fn(u64)>();
};

impl_fn_ptr!();
impl_fn_ptr!(A);
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
