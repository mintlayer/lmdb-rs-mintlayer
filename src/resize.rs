/// The information that will be sent in a callback when a resize happens
#[derive(Debug, Clone)]
pub struct DatabaseResizeInfo {
    pub old_size: u64,
    pub new_size: u64,
    pub occupied_size_before_resize: u64,
}

const DEFAULT_MIN_MAP_SIZE_INCREASE: usize = 1 << 28; // 256 MB
const DEFAULT_MAX_MAP_SIZE_INCREASE: usize = 1 << 31; // 2 GB
const DEFAULT_RESIZE_RATIO: u32 = 100; // 100%, double the current storage
const DEFAULT_RESIZE_PERCENT: f32 = 0.9; // 90% full, causes resize

/// Settings that control resizing the database
#[derive(Debug, Clone)]
pub struct DatabaseResizeSettings {
    /// The minimum amount to increase the size of the database by
    pub min_resize_step: usize,
    /// The maximum amount to increase the size of the database by
    pub max_resize_step: usize,
    /// When a resize is needed and no size is provided, this will be the size ratio to be added compared to the previous size
    /// 100 means 100%, which will double the map size
    pub default_resize_ratio_percentage: u32,
    /// When current_size/total_size crosses this percentage, a resize will be triggered. Value should be in the range: [0, 1]
    pub resize_trigger_percentage: f32,
}

impl Default for DatabaseResizeSettings {
    fn default() -> Self {
        Self::make_default()
    }
}

fn assert_unsigned<T: num::Unsigned>(_: T) {}

impl DatabaseResizeSettings {
    const fn make_default() -> Self {
        Self {
            min_resize_step: DEFAULT_MIN_MAP_SIZE_INCREASE,
            max_resize_step: DEFAULT_MAX_MAP_SIZE_INCREASE,
            default_resize_ratio_percentage: DEFAULT_RESIZE_RATIO,
            resize_trigger_percentage: DEFAULT_RESIZE_PERCENT,
        }
    }

    pub fn validate(&self) {
        // The check below assumes that the type is unsigned
        assert_unsigned(self.min_resize_step);
        if self.min_resize_step == 0 {
            panic!("lmdb: Min step must be positive")
        }

        // The check below assumes that the type is unsigned
        assert_unsigned(self.max_resize_step);
        if self.max_resize_step == 0 {
            panic!("lmdb: Max step must be positive")
        }

        if self.min_resize_step > self.max_resize_step {
            panic!("lmdb: Min step must be <= max step")
        }

        // The check below assumes that the type is unsigned
        assert_unsigned(self.default_resize_ratio_percentage);
        if self.default_resize_ratio_percentage == 0 {
            panic!("lmdb: Resize ratio must be > 0");
        }

        if self.resize_trigger_percentage < 0. {
            panic!("lmdb: Resize trigger percentage must be >=0 ");
        }
    }
}

pub const DEFAULT_RESIZE_SETTINGS: DatabaseResizeSettings = DatabaseResizeSettings::make_default();
