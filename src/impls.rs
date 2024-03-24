macro_rules! get_atomic {
    (($ty: ty, $u_cell: expr) => |$atomic: ident| { $($body:tt)* }) => {
        if core::mem::size_of::<$ty>() == core::mem::size_of::<*mut ()>() {
            use core::sync::atomic::AtomicPtr;

            let $atomic = &*($u_cell.get() as *mut AtomicPtr<()>);
            $($body)*
        }
        else if core::mem::size_of::<$ty>() == core::mem::size_of::<usize>() {
            use core::sync::atomic::AtomicUsize;

            let $atomic = &*($u_cell.get() as *mut AtomicUsize);
            $($body)*
        }
        else {
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

pub(crate) use get_atomic;
