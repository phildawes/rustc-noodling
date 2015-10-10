// see code_chunks  - iterate chunks of code sans comments etc..

#[derive(Clone,Copy)]
enum State {
    StateCode,
    StateComment,
    StateCommentBlock,
    StateString,
    StateChar,
    StateFinished
}

#[derive(Clone,Copy)]
pub struct CodeIndicesIter<'a> {
    src: &'a str,
    pos: usize,
    state: State
}

impl<'a> Iterator for CodeIndicesIter<'a> {
    type Item = (usize, usize);

    #[inline]
    fn next(&mut self) -> Option<(usize, usize)> {
        match self.state {
            State::StateCode => Some(self.code()),
            State::StateComment => Some(self.comment()),
            State::StateCommentBlock  => Some(self.comment_block()),
            State::StateString => Some(self.string()),
            State::StateChar => Some(self.char()),
            State::StateFinished => None
        }
    }
}

impl<'a> CodeIndicesIter<'a> {
    fn code(&mut self) -> (usize, usize) {
        let mut pos = self.pos;
        let start = match self.state {
            State::StateString |
            State::StateChar => { pos-1 }, // include quote
            _ => { pos }
        };
        let src_bytes = self.src.as_bytes();
        for &b in &src_bytes[pos..] {
            pos += 1;
            match b {
                b'/' if src_bytes.len() > pos => match src_bytes[pos] {
                    b'/' => {
                        self.state = State::StateComment;
                        self.pos = pos + 1;
                        return (start, pos-1);
                    },
                    b'*' => {
                        self.state = State::StateCommentBlock;
                        self.pos = pos + 1;
                        return (start, pos-1);
                    },
                    _ => {}
                },
                b'"' => {    // "
                    self.state = State::StateString;
                    self.pos = pos;
                    return (start, pos); // include dblquotes
                },
                b'\'' => {
                    // single quotes are also used for lifetimes, so we need to
                    // be confident that this is not a lifetime.
                    // Look for backslash starting the escape, or a closing quote:
                    if src_bytes.len() > pos + 1 &&
                        (src_bytes[pos] == b'\\' ||
                         src_bytes[pos+1] == b'\'') {
                        self.state = State::StateChar;
                        self.pos = pos;
                        return (start, pos); // include single quote
                    }
                },
                _ => {}
            }
        }

        self.state = State::StateFinished;
        (start, self.src.len())
    }

    fn comment(&mut self) -> (usize, usize) {
        let mut pos = self.pos;
        let src_bytes = self.src.as_bytes();
        for &b in &src_bytes[pos..] {
            pos += 1;
            if b == b'\n' {
                if pos + 2 <= src_bytes.len() && &src_bytes[pos..pos+2] == &[b'/', b'/'] {
                    continue;
                }
                break;
            }
        }
        self.pos = pos;
        self.code()
    }

    fn comment_block(&mut self) -> (usize, usize) {
        let mut nesting_level = 0usize;
        let mut prev = b' ';
        let mut pos = self.pos;
        for &b in &self.src.as_bytes()[pos..] {
            pos += 1;
            match b {
                b'/' if prev == b'*' => {
                    if nesting_level == 0 {
                        break;
                    } else {
                        nesting_level -= 1;
                    }
                },
                b'*' if prev == b'/' => {
                    nesting_level += 1;
                },
                _ => { prev = b; }
            }
        }
        self.pos = pos;
        self.code()
    }

    fn string(&mut self) -> (usize, usize) {
        let src_bytes = self.src.as_bytes();
        let mut pos = self.pos;
        if pos > 1 && src_bytes[pos-2] == b'r' {
            // raw string (eg br"\"): no escape
            match src_bytes[pos..].iter().position(|&b| b == b'"') {
                Some(p) => pos += p+1,
                None    => pos = src_bytes.len()
            }
        } else {
            let mut is_not_escaped = true;
            for &b in &src_bytes[pos..] {
                pos += 1;
                match b {
                    b'"' if is_not_escaped  => { break; }, // "
                    b'\\' => { is_not_escaped = !is_not_escaped; },
                    _ => { is_not_escaped = true; }
                }
            }
        }
        self.pos = pos;
        self.code()
    }

    fn char(&mut self) -> (usize, usize) {
        let mut is_not_escaped = true;
        let mut pos = self.pos;
        for &b in &self.src.as_bytes()[pos..] {
            pos += 1;
            match b {
                b'\'' if is_not_escaped  => { break; },
                b'\\' => { is_not_escaped = !is_not_escaped; },
                _ => { is_not_escaped = true; }
            }
        }
        self.pos = pos;
        self.code()
    }
}

/// Returns indices of chunks of code (minus comments and string contents)
pub fn code_chunks(src: &str) -> CodeIndicesIter {
    CodeIndicesIter { src: src, state: State::StateCode, pos: 0 }
}
