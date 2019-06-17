//! Rpc definition used by example

use easy_jsonrpc::rpc;
use std::sync::atomic::{AtomicI32, Ordering};

// Sync + Send is only for needed the http listener example
#[rpc]
pub trait FrobMachine: Sync + Send {
    fn frob(&self);
    fn unfrob(&self);
    fn get_frob_count(&self) -> i32;
    fn frobn(&self, n: i32);
    fn ultimate_frob(&self, froblist: Vec<i32>);
}

struct FrobMachineImpl {
    frob_count: AtomicI32,
}

impl FrobMachine for FrobMachineImpl {
    fn frob(&self) {
        let was = self.frob_count.fetch_add(1, Ordering::Relaxed);
        eprintln!("Frobbed from {} to {}.", was, was.wrapping_add(1));
    }

    fn unfrob(&self) {
        let was = self.frob_count.fetch_sub(1, Ordering::Relaxed);
        eprintln!("Unfrobbed from {} to {}.", was, was.wrapping_sub(1));
    }

    fn get_frob_count(&self) -> i32 {
        let ret = self.frob_count.load(Ordering::Relaxed);
        eprintln!("Reported frob count of {}.", ret);
        ret
    }

    fn frobn(&self, n: i32) {
        self.frob_count.fetch_add(n, Ordering::Relaxed);
    }

    fn ultimate_frob(&self, froblist: Vec<i32>) {
        use std::convert::TryInto;
        let mut sum: usize = 0;
        eprint!("ULTIMATE FR");
        for frob_val in froblist.iter() {
            self.frob_count.fetch_add(*frob_val, Ordering::Relaxed);
            sum += frob_val
                .wrapping_add(self.frob_count.load(Ordering::Relaxed))
                .try_into()
                .unwrap_or(0);
            let l = b"RROBOOFOROB";
            eprint!("{}", l[sum % l.len()] as char);
        }
        eprintln!("OB!");
    }
}

pub fn create_frob_server() -> Box<dyn FrobMachine> {
    Box::new(FrobMachineImpl {
        frob_count: AtomicI32::new(0),
    })
}
