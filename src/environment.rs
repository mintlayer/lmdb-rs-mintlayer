use libc::{c_uint, size_t};
use std::ffi::CString;
#[cfg(windows)]
use std::ffi::OsStr;
#[cfg(unix)]
use std::os::unix::ffi::OsStrExt;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU32};
use std::sync::Mutex;
use std::{fmt, mem, ptr, result};

use ffi;

use byteorder::{ByteOrder, NativeEndian};

use cursor::Cursor;
use database::Database;
use error::{lmdb_result, Error, Result};
use flags::{DatabaseFlags, EnvironmentFlags};
use transaction::{RoTransaction, RwTransaction, Transaction};

use crate::resize::{DatabaseResizeInfo, DatabaseResizeSettings, DEFAULT_RESIZE_SETTINGS};
use crate::transaction_guard::{ScopedTransactionBlocker, TransactionGuard};

#[cfg(windows)]
/// Adding a 'missing' trait from windows OsStrExt
trait OsStrExtLmdb {
    fn as_bytes(&self) -> &[u8];
}
#[cfg(windows)]
impl OsStrExtLmdb for OsStr {
    fn as_bytes(&self) -> &[u8] {
        &self.to_str().unwrap().as_bytes()
    }
}

/// An LMDB environment.
///
/// An environment supports multiple databases, all residing in the same shared-memory map.
pub struct Environment {
    env: *mut ffi::MDB_env,
    tx_count: AtomicU32,
    tx_blocker_count: AtomicU32,
    tx_blocker_spinlock: AtomicBool,
    db_resize_lock: Mutex<()>,
    dbi_open_mutex: Mutex<()>,
    resize_callback: Option<Box<dyn Fn(DatabaseResizeInfo)>>,
    resize_settings: Option<DatabaseResizeSettings>,
    db_path: PathBuf,
}

impl Environment {
    /// Creates a new builder for specifying options for opening an LMDB environment.
    #[allow(clippy::new_ret_no_self)]
    pub fn new() -> EnvironmentBuilder {
        EnvironmentBuilder {
            flags: EnvironmentFlags::empty(),
            max_readers: None,
            max_dbs: None,
            map_size: None,
            resize_callback: None,
            resize_settings: None,
        }
    }

    /// Returns a raw pointer to the underlying LMDB environment.
    ///
    /// The caller **must** ensure that the pointer is not dereferenced after the lifetime of the
    /// environment.
    pub fn env(&self) -> *mut ffi::MDB_env {
        self.env
    }

    /// Opens a handle to an LMDB database.
    ///
    /// If `name` is `None`, then the returned handle will be for the default database.
    ///
    /// If `name` is not `None`, then the returned handle will be for a named database. In this
    /// case the environment must be configured to allow named databases through
    /// `EnvironmentBuilder::set_max_dbs`.
    ///
    /// The returned database handle may be shared among any transaction in the environment.
    ///
    /// This function will fail with `Error::BadRslot` if called by a thread which has an ongoing
    /// transaction.
    ///
    /// The database name may not contain the null character.
    pub fn open_db<'env>(&'env self, name: Option<&str>) -> Result<Database> {
        let mutex = self.dbi_open_mutex.lock();
        let txn = self.begin_ro_txn()?;
        let db = unsafe { txn.open_db(name)? };
        txn.commit()?;
        drop(mutex);
        Ok(db)
    }

    /// Opens a handle to an LMDB database, creating the database if necessary.
    ///
    /// If the database is already created, the given option flags will be added to it.
    ///
    /// If `name` is `None`, then the returned handle will be for the default database.
    ///
    /// If `name` is not `None`, then the returned handle will be for a named database. In this
    /// case the environment must be configured to allow named databases through
    /// `EnvironmentBuilder::set_max_dbs`.
    ///
    /// The returned database handle may be shared among any transaction in the environment.
    ///
    /// This function will fail with `Error::BadRslot` if called by a thread with an open
    /// transaction.
    pub fn create_db<'env>(&'env self, name: Option<&str>, flags: DatabaseFlags) -> Result<Database> {
        let mutex = self.dbi_open_mutex.lock();
        let txn = self.begin_rw_txn(None)?;
        let db = unsafe { txn.create_db(name, flags)? };
        txn.commit()?;
        drop(mutex);
        Ok(db)
    }

    /// Retrieves the set of flags which the database is opened with.
    ///
    /// The database must belong to to this environment.
    pub fn get_db_flags(&self, db: Database) -> Result<DatabaseFlags> {
        let txn = self.begin_ro_txn()?;
        let mut flags: c_uint = 0;
        unsafe {
            lmdb_result(ffi::mdb_dbi_flags(txn.txn(), db.dbi(), &mut flags))?;
        }
        Ok(DatabaseFlags::from_bits(flags).unwrap())
    }

    /// Create a read-only transaction for use with the environment.
    pub fn begin_ro_txn<'env>(&'env self) -> Result<RoTransaction<'env>> {
        RoTransaction::new(self)
    }

    fn resize_db_if_necessary(&self, headroom: Option<usize>) -> Result<()> {
        let resize_settings = self.resize_settings.as_ref().unwrap_or(&DEFAULT_RESIZE_SETTINGS);

        let mut remaining_required_space = headroom.unwrap_or(resize_settings.default_resize_step);
        let current_iteration_increase = headroom.unwrap_or(resize_settings.default_resize_step);
        while self.needs_resize(headroom)? {
            self.do_resize(current_iteration_increase)?;
            if current_iteration_increase >= remaining_required_space {
                break;
            } else {
                remaining_required_space -= current_iteration_increase;
            }
        }
        Ok(())
    }

    /// Create a read-write transaction for use with the environment. This method will block while
    /// there are any other read-write transactions open on the environment.
    pub fn begin_rw_txn<'env>(&'env self, headroom: Option<usize>) -> Result<RwTransaction<'env>> {
        let _lock = self.db_resize_lock.lock().expect("Database resize mutex lock failed");
        self.resize_db_if_necessary(headroom)?;
        RwTransaction::new(self)
    }

    /// Flush data buffers to disk.
    ///
    /// Data is always written to disk when `Transaction::commit` is called, but the operating
    /// system may keep it buffered. LMDB always flushes the OS buffers upon commit as well, unless
    /// the environment was opened with `MDB_NOSYNC` or in part `MDB_NOMETASYNC`.
    pub fn sync(&mut self, force: bool) -> Result<()> {
        unsafe {
            lmdb_result(ffi::mdb_env_sync(
                self.env(),
                if force {
                    1
                } else {
                    0
                },
            ))
        }
    }

    /// Return the number of transactions currently running; controlled with TransactionGuard objects
    pub(crate) fn tx_count(&self) -> &AtomicU32 {
        &self.tx_count
    }

    /// Return the number of requests to block any new transactions, controlled with ScopedTransactionBlocker
    pub(crate) fn tx_blocker_count(&self) -> &AtomicU32 {
        &self.tx_blocker_count
    }

    /// Return the number of requests to block any new transactions, controlled with ScopedTransactionBlocker
    pub(crate) fn tx_blocker_spinlock(&self) -> &AtomicBool {
        &self.tx_blocker_spinlock
    }

    /// Closes the database handle. Normally unnecessary.
    ///
    /// Closing a database handle is not necessary, but lets `Transaction::open_database` reuse the
    /// handle value. Usually it's better to set a bigger `EnvironmentBuilder::set_max_dbs`, unless
    /// that value would be large.
    ///
    /// ## Safety
    ///
    /// This call is not mutex protected. Databases should only be closed by a single thread, and
    /// only if no other threads are going to reference the database handle or one of its cursors
    /// any further. Do not close a handle if an existing transaction has modified its database.
    /// Doing so can cause misbehavior from database corruption to errors like
    /// `Error::BadValSize` (since the DB name is gone).
    pub unsafe fn close_db(&mut self, db: Database) {
        ffi::mdb_dbi_close(self.env, db.dbi());
    }

    /// Retrieves statistics about this environment.
    pub fn stat(&self) -> Result<Stat> {
        unsafe {
            let mut stat = Stat::new();
            lmdb_try!(ffi::mdb_env_stat(self.env(), stat.mdb_stat()));
            Ok(stat)
        }
    }

    /// Retrieves info about this environment.
    pub fn info(&self) -> Result<Info> {
        unsafe {
            let mut info = Info(mem::zeroed());
            lmdb_try!(ffi::mdb_env_info(self.env(), &mut info.0));
            Ok(info)
        }
    }

    /// Retrieves the total number of pages on the freelist.
    ///
    /// Along with `Environment::info()`, this can be used to calculate the exact number
    /// of used pages as well as free pages in this environment.
    ///
    /// ```ignore
    /// let env = Environment::new().open("/tmp/test").unwrap();
    /// let info = env.info().unwrap();
    /// let stat = env.stat().unwrap();
    /// let freelist = env.freelist().unwrap();
    /// let last_pgno = info.last_pgno() + 1; // pgno is 0 based.
    /// let total_pgs = info.map_size() / stat.page_size() as usize;
    /// let pgs_in_use = last_pgno - freelist;
    /// let pgs_free = total_pgs - pgs_in_use;
    /// ```
    ///
    /// Note:
    ///
    /// * LMDB stores all the freelists in the designated database 0 in each environment,
    ///   and the freelist count is stored at the beginning of the value as `libc::size_t`
    ///   in the native byte order.
    ///
    /// * It will create a read transaction to traverse the freelist database.
    pub fn freelist(&self) -> Result<size_t> {
        let mut freelist: size_t = 0;
        let db = Database::freelist_db();
        let txn = self.begin_ro_txn()?;
        let cursor = txn.open_ro_cursor(db)?;

        for result in cursor.into_iter() {
            let (_key, value) = result?;
            if value.len() < mem::size_of::<size_t>() {
                return Err(Error::Corrupted);
            }

            let s = &value[..mem::size_of::<size_t>()];
            if cfg!(target_pointer_width = "64") {
                freelist += NativeEndian::read_u64(s) as size_t;
            } else {
                freelist += NativeEndian::read_u32(s) as size_t;
            }
        }

        Ok(freelist)
    }

    /// Sets the size of the memory map to use for the environment.
    ///
    /// This could be used to resize the map when the environment is already open.
    ///
    /// Note:
    ///
    /// * No active transactions allowed when performing resizing in this process.
    ///
    /// * The size should be a multiple of the OS page size. Any attempt to set
    ///   a size smaller than the space already consumed by the environment will
    ///   be silently changed to the current size of the used space.
    ///
    /// * In the multi-process case, once a process resizes the map, other
    ///   processes need to either re-open the environment, or call set_map_size
    ///   with size 0 to update the environment. Otherwise, new transaction creation
    ///   will fail with `Error::MapResized`.
    pub fn set_map_size(&self, size: size_t) -> Result<()> {
        unsafe { lmdb_result(ffi::mdb_env_set_mapsize(self.env(), size)) }
    }

    /// Check whether a resize is needed under two conditions:
    /// 1. The headroom + currently used size don't fit in map_size()
    /// 2. More than RESIZE_PERCENTage is used of the database
    fn needs_resize(&self, headroom: Option<usize>) -> Result<bool> {
        // TODO(Sam): test resize checking

        let stat = self.stat()?;
        let env_info = self.info()?;

        let size_used = stat.page_size() as usize - env_info.last_pgno();

        let current_map_size = env_info.map_size();

        let current_percentage_used = size_used as f32 / current_map_size as f32;

        if let Some(given_headroom) = headroom {
            if env_info.map_size() < given_headroom.checked_add(size_used).expect("LMDB size check addition failed") {
                return Ok(true);
            }
        }

        let resize_settings = self.resize_settings.as_ref().unwrap_or(&DEFAULT_RESIZE_SETTINGS);

        Ok(current_percentage_used > resize_settings.resize_trigger_percentage)
    }

    /// Do the resizing. This will pause all transactions (or will dead-lock), then resize
    /// Keep in mind that a single resize step cannot be larger than 1 << 31, due to usize limitations
    /// this is due to the FFI using usize while lmdb uses mdb_size_t, which is always u64
    fn do_resize(&self, increase_size: usize) -> Result<()> {
        // TODO(Sam): test resizing

        let resize_settings = self.resize_settings.as_ref().unwrap_or(&DEFAULT_RESIZE_SETTINGS);
        let increase_size = increase_size.clamp(resize_settings.min_resize_step, resize_settings.min_resize_step);

        let stat = self.stat()?;
        let env_info = self.info()?;

        let old_map_size = env_info.map_size();

        // calculate new map size, and ensure it's an integer of OS page size
        let new_map_size = old_map_size.checked_add(increase_size).expect("LMDB resize size addition failed");
        let new_map_size = new_map_size + new_map_size % stat.page_size() as usize;

        // Check available disk space
        let free_space = fs4::free_space(&self.db_path).expect("Failed to get remaining disk space for db resize");
        let final_increase = new_map_size
            .checked_sub(old_map_size)
            .expect("Resize invariant broken: new_map_size < old_map_size") as u64;
        assert!(
            free_space > final_increase,
            "LMDB Database resize failed. Available free disk space {} bytes is not big enough; required: {} bytes",
            free_space,
            final_increase
        );

        let _tx_blocker = ScopedTransactionBlocker::new(self);
        TransactionGuard::wait_for_transactions_to_finish(self);

        self.set_map_size(new_map_size)?;

        if let Some(resize_callback) = &self.resize_callback {
            resize_callback(DatabaseResizeInfo {
                old_size: old_map_size as u64,
                new_size: new_map_size as u64,
            });
        }

        Ok(())
    }
}

/// Environment statistics.
///
/// Contains information about the size and layout of an LMDB environment or database.
pub struct Stat(ffi::MDB_stat);

impl Stat {
    /// Create a new Stat with zero'd inner struct `ffi::MDB_stat`.
    pub(crate) fn new() -> Stat {
        unsafe { Stat(mem::zeroed()) }
    }

    /// Returns a mut pointer to `ffi::MDB_stat`.
    pub(crate) fn mdb_stat(&mut self) -> *mut ffi::MDB_stat {
        &mut self.0
    }
}

impl Stat {
    /// Size of a database page. This is the same for all databases in the environment.
    #[inline]
    pub fn page_size(&self) -> u32 {
        self.0.ms_psize
    }

    /// Depth (height) of the B-tree.
    #[inline]
    pub fn depth(&self) -> u32 {
        self.0.ms_depth
    }

    /// Number of internal (non-leaf) pages.
    #[inline]
    pub fn branch_pages(&self) -> usize {
        self.0.ms_branch_pages
    }

    /// Number of leaf pages.
    #[inline]
    pub fn leaf_pages(&self) -> usize {
        self.0.ms_leaf_pages
    }

    /// Number of overflow pages.
    #[inline]
    pub fn overflow_pages(&self) -> usize {
        self.0.ms_overflow_pages
    }

    /// Number of data items.
    #[inline]
    pub fn entries(&self) -> usize {
        self.0.ms_entries
    }
}

/// Environment information.
///
/// Contains environment information about the map size, readers, last txn id etc.
pub struct Info(ffi::MDB_envinfo);

impl Info {
    /// Size of memory map.
    #[inline]
    pub fn map_size(&self) -> usize {
        self.0.me_mapsize
    }

    /// Last used page number
    #[inline]
    pub fn last_pgno(&self) -> usize {
        self.0.me_last_pgno
    }

    /// Last transaction ID
    #[inline]
    pub fn last_txnid(&self) -> usize {
        self.0.me_last_txnid
    }

    /// Max reader slots in the environment
    #[inline]
    pub fn max_readers(&self) -> u32 {
        self.0.me_maxreaders
    }

    /// Max reader slots used in the environment
    #[inline]
    pub fn num_readers(&self) -> u32 {
        self.0.me_numreaders
    }
}

unsafe impl Send for Environment {}
unsafe impl Sync for Environment {}

impl fmt::Debug for Environment {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        f.debug_struct("Environment").finish()
    }
}

impl Drop for Environment {
    fn drop(&mut self) {
        // This is a solution for the issue where, very rarely, closing an environment
        // from a thread where a transaction was executed causes a SIGSEGV.
        // This issue was proven and tested in mintlayer-core under rare circumstances
        std::thread::scope(|s| {
            s.spawn(|| unsafe { ffi::mdb_env_close(self.env) })
                .join()
                .expect("Failed to join lmdb Drop for Environment thread");
        });
    }
}

///////////////////////////////////////////////////////////////////////////////////////////////////
//// Environment Builder
///////////////////////////////////////////////////////////////////////////////////////////////////

/// Options for opening or creating an environment.
pub struct EnvironmentBuilder {
    flags: EnvironmentFlags,
    max_readers: Option<c_uint>,
    max_dbs: Option<c_uint>,
    map_size: Option<size_t>,
    resize_callback: Option<Box<dyn Fn(DatabaseResizeInfo)>>,
    resize_settings: Option<DatabaseResizeSettings>,
}

impl EnvironmentBuilder {
    /// Open an environment.
    ///
    /// On UNIX, the database files will be opened with 644 permissions.
    ///
    /// The path may not contain the null character, Windows UNC (Uniform Naming Convention)
    /// paths are not supported either.
    pub fn open(self, path: &Path) -> Result<Environment> {
        self.open_with_permissions(path, 0o644)
    }

    /// Open an environment with the provided UNIX permissions.
    ///
    /// On Windows, the permissions will be ignored.
    ///
    /// The path may not contain the null character, Windows UNC (Uniform Naming Convention)
    /// paths are not supported either.
    pub fn open_with_permissions(self, path: &Path, mode: ffi::mdb_mode_t) -> Result<Environment> {
        let mut env: *mut ffi::MDB_env = ptr::null_mut();
        unsafe {
            lmdb_try!(ffi::mdb_env_create(&mut env));
            if let Some(max_readers) = self.max_readers {
                lmdb_try_with_cleanup!(ffi::mdb_env_set_maxreaders(env, max_readers), ffi::mdb_env_close(env))
            }
            if let Some(max_dbs) = self.max_dbs {
                lmdb_try_with_cleanup!(ffi::mdb_env_set_maxdbs(env, max_dbs), ffi::mdb_env_close(env))
            }
            if let Some(map_size) = self.map_size {
                lmdb_try_with_cleanup!(ffi::mdb_env_set_mapsize(env, map_size), ffi::mdb_env_close(env))
            }
            let path = match CString::new(path.as_os_str().as_bytes()) {
                Ok(path) => path,
                Err(..) => return Err(::Error::Invalid),
            };
            lmdb_try_with_cleanup!(
                ffi::mdb_env_open(env, path.as_ptr(), self.flags.bits(), mode),
                ffi::mdb_env_close(env)
            );
        }
        Ok(Environment {
            env,
            tx_count: AtomicU32::new(0),
            tx_blocker_count: AtomicU32::new(0),
            tx_blocker_spinlock: AtomicBool::new(false),
            db_resize_lock: Mutex::new(()),
            dbi_open_mutex: Mutex::new(()),
            resize_callback: self.resize_callback,
            resize_settings: self.resize_settings,
            db_path: path.to_owned(),
        })
    }

    /// Sets the provided options in the environment.
    pub fn set_flags(mut self, flags: EnvironmentFlags) -> EnvironmentBuilder {
        self.flags = flags;
        self
    }

    /// Sets the maximum number of threads or reader slots for the environment.
    ///
    /// This defines the number of slots in the lock table that is used to track readers in the
    /// the environment. The default is 126. Starting a read-only transaction normally ties a lock
    /// table slot to the current thread until the environment closes or the thread exits. If
    /// `MDB_NOTLS` is in use, `Environment::open_txn` instead ties the slot to the `Transaction`
    /// object until it or the `Environment` object is destroyed.
    pub fn set_max_readers(mut self, max_readers: c_uint) -> EnvironmentBuilder {
        self.max_readers = Some(max_readers);
        self
    }

    /// Sets the maximum number of named databases for the environment.
    ///
    /// This function is only needed if multiple databases will be used in the
    /// environment. Simpler applications that use the environment as a single
    /// unnamed database can ignore this option.
    ///
    /// Currently a moderate number of slots are cheap but a huge number gets
    /// expensive: 7-120 words per transaction, and every `Transaction::open_db`
    /// does a linear search of the opened slots.
    pub fn set_max_dbs(mut self, max_dbs: c_uint) -> EnvironmentBuilder {
        self.max_dbs = Some(max_dbs);
        self
    }

    /// Sets the size of the memory map to use for the environment.
    ///
    /// The size should be a multiple of the OS page size. The default is
    /// 1048576 bytes. The size of the memory map is also the maximum size
    /// of the database. The value should be chosen as large as possible,
    /// to accommodate future growth of the database. It may be increased at
    /// later times.
    ///
    /// Any attempt to set a size smaller than the space already consumed
    /// by the environment will be silently changed to the current size of the used space.
    pub fn set_map_size(mut self, map_size: size_t) -> EnvironmentBuilder {
        self.map_size = Some(map_size);
        self
    }

    /// Set the function that will be called when a database resize happens
    pub fn set_resize_callback(mut self, callback: Option<Box<dyn Fn(DatabaseResizeInfo)>>) -> EnvironmentBuilder {
        self.resize_callback = callback;
        self
    }

    /// The settings that control when and how resize happens
    pub fn set_resize_settings(mut self, settings: DatabaseResizeSettings) -> EnvironmentBuilder {
        self.resize_settings = Some(settings);
        self
    }
}

#[cfg(test)]
mod test {

    extern crate byteorder;

    use self::byteorder::{ByteOrder, LittleEndian};
    use tempdir::TempDir;

    use flags::*;

    use super::*;

    #[test]
    fn test_open() {
        let dir = TempDir::new("test").unwrap();

        // opening non-existent env with read-only should fail
        assert!(Environment::new().set_flags(EnvironmentFlags::READ_ONLY).open(dir.path()).is_err());

        // opening non-existent env should succeed
        assert!(Environment::new().open(dir.path()).is_ok());

        // opening env with read-only should succeed
        assert!(Environment::new().set_flags(EnvironmentFlags::READ_ONLY).open(dir.path()).is_ok());
    }

    #[test]
    fn test_begin_txn() {
        let dir = TempDir::new("test").unwrap();

        {
            // writable environment
            let env = Environment::new().open(dir.path()).unwrap();

            assert!(env.begin_rw_txn(None).is_ok());
            assert!(env.begin_ro_txn().is_ok());
        }

        {
            // read-only environment
            let env = Environment::new().set_flags(EnvironmentFlags::READ_ONLY).open(dir.path()).unwrap();

            assert!(env.begin_rw_txn(None).is_err());
            assert!(env.begin_ro_txn().is_ok());
        }
    }

    #[test]
    fn test_open_db() {
        let dir = TempDir::new("test").unwrap();
        let env = Environment::new().set_max_dbs(1).open(dir.path()).unwrap();

        assert!(env.open_db(None).is_ok());
        assert!(env.open_db(Some("testdb")).is_err());
    }

    #[test]
    fn test_create_db() {
        let dir = TempDir::new("test").unwrap();
        let env = Environment::new().set_max_dbs(11).open(dir.path()).unwrap();
        assert!(env.open_db(Some("testdb")).is_err());
        assert!(env.create_db(Some("testdb"), DatabaseFlags::empty()).is_ok());
        assert!(env.open_db(Some("testdb")).is_ok())
    }

    #[test]
    fn test_close_database() {
        let dir = TempDir::new("test").unwrap();
        let mut env = Environment::new().set_max_dbs(10).open(dir.path()).unwrap();

        let db = env.create_db(Some("db"), DatabaseFlags::empty()).unwrap();
        unsafe {
            env.close_db(db);
        }
        assert!(env.open_db(Some("db")).is_ok());
    }

    #[test]
    fn test_sync() {
        let dir = TempDir::new("test").unwrap();
        {
            let mut env = Environment::new().open(dir.path()).unwrap();
            assert!(env.sync(true).is_ok());
        }
        {
            let mut env = Environment::new().set_flags(EnvironmentFlags::READ_ONLY).open(dir.path()).unwrap();
            assert!(env.sync(true).is_err());
        }
    }

    #[test]
    fn test_stat() {
        let dir = TempDir::new("test").unwrap();
        let env = Environment::new().open(dir.path()).unwrap();

        // Stats should be empty initially.
        let stat = env.stat().unwrap();
        assert_eq!(stat.page_size(), page_size::get() as u32);
        assert_eq!(stat.depth(), 0);
        assert_eq!(stat.branch_pages(), 0);
        assert_eq!(stat.leaf_pages(), 0);
        assert_eq!(stat.overflow_pages(), 0);
        assert_eq!(stat.entries(), 0);

        let db = env.open_db(None).unwrap();

        // Write a few small values.
        for i in 0..64 {
            let mut value = [0u8; 8];
            LittleEndian::write_u64(&mut value, i);
            let mut tx = env.begin_rw_txn(None).expect("begin_rw_txn");
            tx.put(db, &value, &value, WriteFlags::default()).expect("tx.put");
            tx.commit().expect("tx.commit")
        }

        // Stats should now reflect inserted values.
        let stat = env.stat().unwrap();
        assert_eq!(stat.page_size(), page_size::get() as u32);
        assert_eq!(stat.depth(), 1);
        assert_eq!(stat.branch_pages(), 0);
        assert_eq!(stat.leaf_pages(), 1);
        assert_eq!(stat.overflow_pages(), 0);
        assert_eq!(stat.entries(), 64);
    }

    #[test]
    fn test_info() {
        let map_size = 1024 * 1024;
        let dir = TempDir::new("test").unwrap();
        let env = Environment::new().set_map_size(map_size).open(dir.path()).unwrap();

        let info = env.info().unwrap();
        assert_eq!(info.map_size(), map_size);
        assert_eq!(info.last_pgno(), 1);
        assert_eq!(info.last_txnid(), 0);
        // The default max readers is 126.
        assert_eq!(info.max_readers(), 126);
        assert_eq!(info.num_readers(), 0);
    }

    #[test]
    fn test_freelist() {
        let dir = TempDir::new("test").unwrap();
        let env = Environment::new().open(dir.path()).unwrap();

        let db = env.open_db(None).unwrap();
        let mut freelist = env.freelist().unwrap();
        assert_eq!(freelist, 0);

        // Write a few small values.
        for i in 0..64 {
            let mut value = [0u8; 8];
            LittleEndian::write_u64(&mut value, i);
            let mut tx = env.begin_rw_txn(None).expect("begin_rw_txn");
            tx.put(db, &value, &value, WriteFlags::default()).expect("tx.put");
            tx.commit().expect("tx.commit")
        }
        let mut tx = env.begin_rw_txn(None).expect("begin_rw_txn");
        tx.clear_db(db).expect("clear");
        tx.commit().expect("tx.commit");

        // Freelist should not be empty after clear_db.
        freelist = env.freelist().unwrap();
        assert!(freelist > 0);
    }

    #[test]
    fn test_set_map_size() {
        let dir = TempDir::new("test").unwrap();
        let env = Environment::new().open(dir.path()).unwrap();

        let mut info = env.info().unwrap();
        let default_size = info.map_size();

        // Resizing to 0 merely reloads the map size
        env.set_map_size(0).unwrap();
        info = env.info().unwrap();
        assert_eq!(info.map_size(), default_size);

        env.set_map_size(2 * default_size).unwrap();
        info = env.info().unwrap();
        assert_eq!(info.map_size(), 2 * default_size);

        env.set_map_size(4 * default_size).unwrap();
        info = env.info().unwrap();
        assert_eq!(info.map_size(), 4 * default_size);

        // Decreasing is also fine if the space hasn't been consumed.
        env.set_map_size(2 * default_size).unwrap();
        info = env.info().unwrap();
        assert_eq!(info.map_size(), 2 * default_size);
    }
}
