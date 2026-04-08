use std::path::{Path, PathBuf};
use std::rc::Rc;

use smol_str::SmolStr;

/// A module path is just a list of module segments. E.g. `Fir/Prelude` is a path with two segments:
/// `["Fir", "Prelude"]`.
///
/// This type is reference counted, and so cheap to clone.
///
/// Note that module paths are not canonicalized. There can be multiple `ModulePath` objects with
/// the same segments.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ModulePath {
    segments: Rc<[SmolStr]>,
}

impl ModulePath {
    pub fn new(segments: Vec<SmolStr>) -> Self {
        ModulePath {
            segments: Rc::from(segments),
        }
    }

    pub fn segments(&self) -> &[SmolStr] {
        &self.segments
    }

    pub fn from_file_path(path: &Path) -> Self {
        let segments: Vec<SmolStr> = path
            .with_extension("")
            .iter()
            .map(|c| SmolStr::new(c.to_str().unwrap()))
            .collect();
        ModulePath {
            segments: Rc::from(segments),
        }
    }

    pub fn to_file_path(&self) -> PathBuf {
        let mut path = PathBuf::new();
        for seg in self.segments.iter() {
            path.push(seg.as_str());
        }
        path.set_extension("fir");
        path
    }
}

impl std::fmt::Display for ModulePath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, seg) in self.segments.iter().enumerate() {
            if i > 0 {
                f.write_str("/")?;
            }
            f.write_str(seg)?;
        }
        Ok(())
    }
}
