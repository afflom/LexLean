//! Canonical artifacts: JSON form, content identity, source maps, coverage,
//! and build manifests (SPEC.md §20, §21).

pub mod canonical_json;
pub mod content_id;
pub mod manifest;
pub mod source_map;

/// Durably record a directory rename (§21.8): open the parent directory
/// and `fsync` it where the platform supports directory synchronization.
/// A platform that cannot open directories for synchronization simply
/// completes the rename without the extra barrier.
pub fn fsync_dir(directory: &std::path::Path) {
    #[cfg(unix)]
    {
        if let Ok(handle) = std::fs::File::open(directory) {
            let _ = handle.sync_all();
        }
    }
    #[cfg(not(unix))]
    {
        let _ = directory;
    }
}
