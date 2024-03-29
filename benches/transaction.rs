use criterion::{black_box, criterion_group, criterion_main, Bencher, Criterion};

use lmdb_sys as ffi;

mod utils;

use ffi::*;
use libc::size_t;
use lmdb::{Transaction, WriteFlags};
use rand::{seq::SliceRandom, SeedableRng};
use std::ptr;
use utils::*;

fn bench_get_rand(b: &mut Bencher) {
    let n = 100u32;
    let (_dir, env) = setup_bench_db(n);
    let db = env.open_db(None).unwrap();
    let txn = env.begin_ro_txn().unwrap();

    let mut keys: Vec<String> = (0..n).map(get_key).collect();
    keys.shuffle(&mut rand::rngs::StdRng::from_entropy());

    b.iter(|| {
        let mut i = 0usize;
        for key in &keys {
            i += txn.get(db, key).unwrap().len();
        }
        black_box(i);
    });
}

fn bench_get_rand_raw(b: &mut Bencher) {
    let n = 100u32;
    let (_dir, env) = setup_bench_db(n);
    let db = env.open_db(None).unwrap();
    let _txn = env.begin_ro_txn().unwrap();

    let mut keys: Vec<String> = (0..n).map(get_key).collect();
    keys.shuffle(&mut rand::rngs::StdRng::from_entropy());

    let dbi = db.dbi();
    let txn = _txn.txn();

    let mut key_val: MDB_val = MDB_val {
        mv_size: 0,
        mv_data: ptr::null_mut(),
    };
    let mut data_val: MDB_val = MDB_val {
        mv_size: 0,
        mv_data: ptr::null_mut(),
    };

    b.iter(|| unsafe {
        let mut i: size_t = 0;
        for key in &keys {
            key_val.mv_size = key.len() as size_t;
            key_val.mv_data = key.as_bytes().as_ptr() as *mut _;

            mdb_get(txn, dbi, &mut key_val, &mut data_val);

            i += key_val.mv_size;
        }
        core::hint::black_box(i);
    });
}

fn bench_put_rand(b: &mut Bencher) {
    let n = 100u32;
    let (_dir, env) = setup_bench_db(0);
    let db = env.open_db(None).unwrap();

    let mut items: Vec<(String, String)> = (0..n).map(|n| (get_key(n), get_data(n))).collect();
    items.shuffle(&mut rand::rngs::StdRng::from_entropy());

    b.iter(|| {
        let mut txn = env.begin_rw_txn(None).unwrap();
        for &(ref key, ref data) in items.iter() {
            txn.put(db, key, data, WriteFlags::empty()).unwrap();
        }
        txn.abort();
    });
}

fn bench_put_rand_raw(b: &mut Bencher) {
    let n = 100u32;
    let (_dir, _env) = setup_bench_db(0);
    let db = _env.open_db(None).unwrap();

    let mut items: Vec<(String, String)> = (0..n).map(|n| (get_key(n), get_data(n))).collect();
    items.shuffle(&mut rand::rngs::StdRng::from_entropy());

    let dbi = db.dbi();
    let env = _env.env();

    let mut key_val: MDB_val = MDB_val {
        mv_size: 0,
        mv_data: ptr::null_mut(),
    };
    let mut data_val: MDB_val = MDB_val {
        mv_size: 0,
        mv_data: ptr::null_mut(),
    };

    b.iter(|| unsafe {
        let mut txn: *mut MDB_txn = ptr::null_mut();
        mdb_txn_begin(env, ptr::null_mut(), 0, &mut txn);

        let mut i: ::libc::c_int = 0;
        for &(ref key, ref data) in items.iter() {
            key_val.mv_size = key.len() as size_t;
            key_val.mv_data = key.as_bytes().as_ptr() as *mut _;
            data_val.mv_size = data.len() as size_t;
            data_val.mv_data = data.as_bytes().as_ptr() as *mut _;

            i += mdb_put(txn, dbi, &mut key_val, &mut data_val, 0);
        }
        assert_eq!(0, i);
        mdb_txn_abort(txn);
    });
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("bench_get_rand", bench_get_rand);
    c.bench_function("bench_get_rand_raw", bench_get_rand_raw);
    c.bench_function("bench_put_rand", bench_put_rand);
    c.bench_function("bench_put_rand_raw", bench_put_rand_raw);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
