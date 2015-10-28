use syntax::codemap;
use std::path::Path;
use std::io;
use std::io::Read;
use codeiter;

pub struct StrippedFileLoader {
    pub fname: String,
    pub tmpfname: String,
    pub coords: (usize,usize),   // coords of function to leave alone
}

// TODO: this doesn't play well with multibyte chars
pub fn coords_to_byteoffset(src: &str, mut linenum: usize, col: usize) -> usize {
    let mut point = 0;
    for line in src.lines() {
        linenum -= 1;
        if linenum == 0 { break }
        point += line.len() + 1;  // +1 for the \n
    }
    point + col
}

fn mask(result: &mut String, src: &str, (from, to): (usize,usize)) {
    
    for c in src[from..to].as_bytes() {
        if *c == b'\n' {
            result.push_str("\n");
        } else {
            result.push_str(" ");
        }
    }
}


fn handle_blob(src: &str, out: &mut String, prev: &mut usize, 
               blockstart: usize, end: usize, byteoffset: usize) {
    
    for (blobstart,blobend) in codeiter::iter_stmts(&src[blockstart..end]) {
        let start = blobstart + blockstart;
        let end = blobend + blockstart;

        let blob = &src[start..end];

        if blob.starts_with("impl") {
            if let Some(bracepos) = blob.find("{") {
                assert_eq!("}", &src[end-1..end]);
                handle_blob(src, out, prev, start+bracepos+1, end-1, byteoffset);
            }

        } else if let Some(_) = find_keyword(blob, "fn") {

            if start < byteoffset && end > byteoffset {
                // we need the code in this function. Don't strip it!
                continue;
            }

            if let Some(bracepos) = blob.find("{") {
                out.push_str(&src[*prev..(start + bracepos + 1)]);
                mask(out, src, ((start+bracepos+1), (end-1)));
                assert_eq!("}", &src[end-1..end]);
                out.push_str("}");
                *prev = end;
            }
        }
    }
}

impl codemap::FileLoader for StrippedFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        ::std::fs::metadata(path).is_ok()
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        //println!("PHIL reading file: {:?}",path);

        let realpath;
        if path.to_str().unwrap() == self.fname {
            realpath = Path::new(&self.tmpfname);
        } else {
            realpath = path;
        }

        let mut src = String::new();
        try!(try!(::std::fs::File::open(realpath)).read_to_string(&mut src));
        
        let byteoffset = 
            if path.to_str().unwrap() == self.fname {
                let b = coords_to_byteoffset(&src, self.coords.0, self.coords.1);
                println!("PHIL byteoffset is {} ({:?})", b, self.coords);
                b
            } else {
                0
            };
           
        let mut out = String::with_capacity(src.len());
        let mut prev = 0;
        handle_blob(&src, &mut out, &mut prev, 0, src.len(), byteoffset);
        out.push_str(&src[prev..]);

        assert_eq!(src.len(), out.len());

        //println!("PHIL |{}|",out);
        Ok(out)
    }
}


fn find_keyword(src: &str, pattern: &str)-> Option<usize> {
    // search for "^(pub\s+)?(unsafe\s+)?pattern\s+"

    let mut start = 0usize;

    // optional (pub\s+)?(unsafe\s+)?
    for pat in ["pub", "unsafe"].into_iter() {
        if src[start..].starts_with(pat) {
            // remove whitespaces ... must have one at least
            start += pat.len();
            let oldstart = start;
            for &b in src[start..].as_bytes() {
                match b {
                    b' '|b'\r'|b'\n'|b'\t' => start += 1,
                    _ => break
                }
            }
            if start == oldstart { return None; }
        }
    }

    // mandatory pattern\s+
    if src[start..].starts_with(pattern) {
        // remove whitespaces ... must have one at least
        start += pattern.len();
        let oldstart = start;
        for &b in src[start..].as_bytes() {
            match b {
                b' '|b'\r'|b'\n'|b'\t' => start += 1,
                _ => break
            }
        }
        if start == oldstart { return None; }
    } else {
        return None;
    }
    Some(start)
}

// Load just the function that the coordinates reference
pub fn load_blob(path: &Path, coords: (usize, usize)) -> io::Result<String> {
    let mut src = String::new();
    try!(try!(::std::fs::File::open(path)).read_to_string(&mut src));    
    match extract_blob(&src, 0, src.len(),
                       coords_to_byteoffset(&src, coords.0, coords.1)) {
        Some(n) => Ok(n.to_owned()),
        None => Err(io::Error::new(io::ErrorKind::NotFound, "Couldn't find an blob of code matching the coordinates"))
    }
}


fn extract_blob<'a>(src: &'a str, blockstart: usize, end: usize, 
                    byteoffset: usize) -> Option<&'a str> {
    
    for (blobstart,blobend) in codeiter::iter_stmts(&src[blockstart..end]) {
        let start = blobstart + blockstart;
        let end = blobend + blockstart;

        let blob = &src[start..end];

        if blob.starts_with("impl") {
            if let Some(bracepos) = blob.find("{") {
                assert_eq!("}", &src[end-1..end]);
                let a = extract_blob(src, start+bracepos+1, end-1, byteoffset);
                if let Some(_) = a {
                    return a;
                }
            }

        } else if let Some(_) = find_keyword(blob, "fn") {
            if start < byteoffset && end > byteoffset {
                // we need the code in this function. Don't strip it!
                return Some(&src[start..end]);
            }
        }
    }
    None
}

