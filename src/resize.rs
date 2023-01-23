/// The information that will be sent in a callback when a resize happens
#[derive(Debug, Clone)]
pub struct DatabaseResizeInfo {
    pub old_size: u64,
    pub new_size: u64,
    pub occupied_size_before_resize: u64,
}

const DEFAULT_MIN_MAP_SIZE_INCREASE: usize = 1 << 28;
const DEFAULT_MAX_MAP_SIZE_INCREASE: usize = 1 << 31;
const DEFAULT_RESIZE_VALUE: usize = 1 << 28;
const DEFAULT_RESIZE_PERCENT: f32 = 0.9;

/// Settings that control resizing the database
#[derive(Debug, Clone)]
pub struct DatabaseResizeSettings {
    /// The minimum amount to increase the size of the database by
    pub min_resize_step: usize,
    /// The maximum amount to increase the size of the database by
    pub max_resize_step: usize,
    /// When a resize is needed and no size is provided, this will be the size to increase by
    pub default_resize_step: usize,
    /// When current_size/total_size crosses this percentage, a resize will be triggered. Value should be in the range: [0, 1]
    pub resize_trigger_percentage: f32,
}

impl Default for DatabaseResizeSettings {
    fn default() -> Self {
        Self::make_default()
    }
}

impl DatabaseResizeSettings {
    const fn make_default() -> Self {
        Self {
            min_resize_step: DEFAULT_MIN_MAP_SIZE_INCREASE,
            max_resize_step: DEFAULT_MAX_MAP_SIZE_INCREASE,
            default_resize_step: DEFAULT_RESIZE_VALUE,
            resize_trigger_percentage: DEFAULT_RESIZE_PERCENT,
        }
    }
}

pub const DEFAULT_RESIZE_SETTINGS: DatabaseResizeSettings = DatabaseResizeSettings::make_default();
