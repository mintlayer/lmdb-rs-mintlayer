use std::sync::atomic::Ordering;

use crate::Environment;

#[must_use = "TransactionGuard has no effect without holding its object"]
pub struct TransactionGuard<'a> {
    env: &'a Environment,
}

/// A transaction guard is a static global counter that keeps track of all transactions currently open
/// It can be used for operations that need to wait for all transactions to be closed, such as map-resize
impl<'a> TransactionGuard<'a> {
    pub fn new(env: &'a Environment) -> Self {
        ScopedTransactionBlocker::wait_for_all_blockers(env);
        env.tx_count().fetch_add(1, Ordering::Relaxed);
        Self {
            env,
        }
    }

    pub fn wait_for_transactions_to_finish(env: &'a Environment) {
        while env.tx_count().load(Ordering::Relaxed) > 0 {}
    }
}

impl<'a> Drop for TransactionGuard<'a> {
    fn drop(&mut self) {
        self.env.tx_count().fetch_sub(1, Ordering::Relaxed);
    }
}

#[must_use = "ScopedTransactionBlocker has no effect without holding its object"]
pub struct ScopedTransactionBlocker<'a> {
    env: &'a Environment,
}

/// A ScopedTransactionBlocked is a struct that is used to prevent new transactions from being created
/// As long as an instance is alive, TransactionGuard will prevent the creation of new transactions
impl<'a> ScopedTransactionBlocker<'a> {
    pub fn new(env: &'a Environment) -> Self {
        env.tx_blocker_count().fetch_add(1, Ordering::Relaxed);
        Self {
            env,
        }
    }

    pub fn wait_for_all_blockers(env: &'a Environment) {
        while env.tx_blocker_count().load(Ordering::Relaxed) > 0 {}
    }
}

impl<'a> Drop for ScopedTransactionBlocker<'a> {
    fn drop(&mut self) {
        self.env.tx_blocker_count().fetch_sub(1, Ordering::Relaxed);
    }
}

// TODO(Sam): tests
