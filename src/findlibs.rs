use std::path::{Path, PathBuf};
use std::fs::File;

pub fn find_cargo_tomlfile(currentfile: &Path) -> Option<PathBuf> {
    let mut f = currentfile.to_path_buf();
    f.push("Cargo.toml");
    if path_exists(f.as_path()) {
        Some(f)
    } else {
        if f.pop() && f.pop() {
            find_cargo_tomlfile(&f)
        } else {
            None
        }
    }
}

pub fn find_librs(currentfile: &Path) -> Option<PathBuf> {
    let mut f = currentfile.to_path_buf();
    f.push("lib.rs");
    if path_exists(f.as_path()) {
        Some(f)
    } else {
        if f.pop() && f.pop() {
            find_librs(&f)
        } else {
            None
        }
    }
    
}

pub fn main_file(cargofile: &Path) -> PathBuf {
    let mut f = cargofile.to_path_buf();
    f.pop();
    f.push("src/main.rs");
    f
}

pub fn dependency_path(cargofile: &Path) -> PathBuf {
    let mut f = cargofile.to_path_buf();
    f.pop();
    f.push("target/release/deps");
    f
}


pub fn list_libs(cargofile: &Path) -> Vec<(String,PathBuf)> {
    let mut f = cargofile.to_path_buf();
    f.pop();
    f.push("target/release/deps");
    let mut v = Vec::new();
    for p in ::std::fs::read_dir(f).unwrap() {
        let p = p.unwrap();

        let fname = p.file_name().to_str().unwrap().to_string();
        // this is scrappy
        let libname = fname.split("-").nth(0).unwrap()[3..].to_string();

        v.push((libname, p.path()));
    }
    v
}

// PD: short term replacement for path.exists() (PathExt trait). Replace once
// that stabilizes
pub fn path_exists<P: AsRef<Path>>(path: P) -> bool {
    is_dir(&path) || File::open(path).is_ok()
}

// PD: short term replacement for path.is_dir() (PathExt trait). Replace once
// that stabilizes
pub fn is_dir<P: AsRef<Path>>(path: P) -> bool {
    ::std::fs::metadata(path).map(|info| info.is_dir()).unwrap_or(false)
}


#[allow(dead_code)]
fn main() {
    let p = Path::new("/home/pld/src/rust/rustc-noodling/src/try2.rs");
    let p = find_cargo_tomlfile(p);
    println!("p {:?}",p);
    let libs = list_libs(&p.unwrap());
    println!("libs {:?}",libs);
}
