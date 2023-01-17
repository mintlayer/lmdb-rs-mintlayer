use std::{
    marker::PhantomData,
    sync::atomic::{AtomicU32, Ordering},
};

static TRANSACTION_COUNT: AtomicU32 = AtomicU32::new(0);
static TRANSACTIONS_BLOCKERS: AtomicU32 = AtomicU32::new(0);

#[must_use = "TransactionGuard has no effect without holding its object"]
pub struct TransactionGuard {
    private: PhantomData<()>,
}

/// A transaction guard is a static global counter that keeps track of all transactions currently open
/// It can be used for operations that need to wait for all transactions to be closed, such as map-resize
impl TransactionGuard {
    pub fn new() -> Self {
        ScopedTransactionBlocker::wait_for_all_blockers();
        TRANSACTION_COUNT.fetch_add(1, Ordering::Relaxed);
        Self {
            private: Default::default(),
        }
    }

    pub fn wait_for_transactions_to_finish() {
        while TRANSACTION_COUNT.load(Ordering::Relaxed) > 0 {}
    }
}

impl Drop for TransactionGuard {
    fn drop(&mut self) {
        TRANSACTION_COUNT.fetch_sub(1, Ordering::Relaxed);
    }
}

#[must_use = "ScopedTransactionBlocker has no effect without holding its object"]
pub struct ScopedTransactionBlocker {
    private: PhantomData<()>,
}

/// A ScopedTransactionBlocked is a struct that is used to prevent new transactions from being created
/// As long as an instance is alive, TransactionGuard will prevent the creation of new transactions
impl ScopedTransactionBlocker {
    pub fn new() -> Self {
        TRANSACTIONS_BLOCKERS.fetch_add(1, Ordering::Relaxed);
        Self {
            private: Default::default(),
        }
    }

    pub fn wait_for_all_blockers() {
        while TRANSACTIONS_BLOCKERS.load(Ordering::Relaxed) > 0 {}
    }
}

impl Drop for ScopedTransactionBlocker {
    fn drop(&mut self) {
        TRANSACTIONS_BLOCKERS.fetch_sub(1, Ordering::Relaxed);
    }
}

// TODO(Sam): tests
