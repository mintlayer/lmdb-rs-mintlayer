//! Idiomatic and safe APIs for interacting with the
//! [Lightning Memory-mapped Database (LMDB)](https://symas.com/lmdb).

#![deny(missing_docs)]

extern crate byteorder;
extern crate libc;
extern crate lmdb_sys as ffi;

#[cfg(test)]
extern crate tempdir;
#[macro_use]
extern crate bitflags;

pub use cursor::{
    Cursor,
    Iter,
    RoCursor,
    RwCursor,
};
pub use database::Database;
pub use environment::{
    Environment,
    EnvironmentBuilder,
    Info,
    Stat,
};
pub use error::{
    Error,
    Result,
};
pub use flags::*;
pub use transaction::{
    InactiveTransaction,
    RoTransaction,
    RwTransaction,
    Transaction,
};

macro_rules! lmdb_try {
    ($expr:expr) => {{
        match $expr {
            ::ffi::MDB_SUCCESS => (),
            err_code => return Err(::Error::from_err_code(err_code)),
        }
    }};
}

macro_rules! lmdb_try_with_cleanup {
    ($expr:expr, $cleanup:expr) => {{
        match $expr {
            ::ffi::MDB_SUCCESS => (),
            err_code => {
                let _ = $cleanup;
                return Err(::Error::from_err_code(err_code));
            },
        }
    }};
}

#[cfg(not(target_pointer_width = "64"))]
compile_error!("Mintlayer with lmdb backend can only be compiled on 64-bit systems. Either seek an alternative storage backend or use a 64-bit system.");

mod cursor;
mod database;
mod environment;
mod error;
mod flags;
mod transaction;
mod transaction_guard;

#[cfg(test)]
mod test_utils {

    use byteorder::{
        ByteOrder,
        LittleEndian,
    };
    use tempdir::TempDir;

    use super::*;

    /// Regression test for https://github.com/danburkert/lmdb-rs/issues/21.
    /// This test reliably segfaults when run against lmdb compiled with opt level -O3 and newer
    /// GCC compilers.
    #[test]
    fn issue_21_regression() {
        const HEIGHT_KEY: [u8; 1] = [0];

        let dir = TempDir::new("test").unwrap();

        let env = Environment::new().
        set_max_dbs(2).
        set_map_size(1_000_000).
        open(dir.path()).expect("open lmdb env");

        let index = env.create_db(None, DatabaseFlags::DUP_SORT).expect("open index db");

        for height in 0..1000 {
            let mut value = [0u8; 8];
            LittleEndian::write_u64(&mut value, height);
            let mut tx = env.begin_rw_txn(None).expect("begin_rw_txn");
            tx.put(index, &HEIGHT_KEY, &value, WriteFlags::empty()).expect("tx.put");
            tx.commit().expect("tx.commit")
        }
    }
}
