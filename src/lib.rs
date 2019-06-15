use std::os::unix::ffi::{OsStringExt, OsStrExt};
use std::ffi::{OsStr, OsString};


pub trait OsStrTools {
    fn split(&self, pat: &OsStr) -> Vec<OsString>;
    fn split_lines(&self) -> Vec<OsString>;
    fn replace(&self, from: &OsStr, to: &OsStr) -> OsString;
    fn trim_last_space(&self) -> OsString;
    fn trim_end_newlines(&self) -> &OsStr;
    fn contains_osstr(&self, pat: &OsStr) -> bool;
    fn position(&self, pat: &OsStr) -> Option<usize>;
    fn splice_quoted(&self, from: &OsStr, to: Vec<OsString>) -> Vec<OsString>;
    fn splice_quoted_single(&self, from: &OsStr, to: Vec<OsString>) -> Vec<OsString>;
    fn splice_with(&self, from: &OsStr, to: Vec<OsString>) -> Vec<OsString>;
    fn quote(&self) -> OsString;
    fn quote_single(&self) -> OsString;
}

impl OsStrTools for OsStr {
    fn split(&self, pat: &OsStr) -> Vec<OsString> {
        let orig_string = self.as_bytes().to_vec();
        let pat = pat.as_bytes().to_vec();
        let pat_len = pat.len();

        let split_string = orig_string
            .windows(pat_len)
            .enumerate()
            .fold(Vec::new(), |mut split_pos, (i, chars)| {
                if chars == pat.as_slice() {
                    if split_pos.len() == 0 {
                        split_pos.push((0, i));
                    } else {
                        let len = split_pos.len();
                        let last_split = split_pos[len-1].1;
                        split_pos.push((last_split, i));
                    }
                }
                split_pos
            }).iter()
            .map(|(start, end)| {
                OsString::from_vec(orig_string[*start..*end]
                                   .to_vec()).replace(&OsString::from_vec(pat.clone()),
                                                      &OsString::from(""))
            }).collect();
        split_string
    }

    fn split_lines(&self) -> Vec<OsString> {
        let newline = OsString::from("\n");
        self.split(&newline)
    }

    fn quote(&self) -> OsString {
        let mut string = self.as_bytes().to_vec();
        let mut quote = "\"".as_bytes().to_vec();

        let mut quoted = vec![];
        quoted.append(&mut quote.clone());
        quoted.append(&mut string);
        quoted.append(&mut quote);

        OsString::from_vec(quoted)
    }

    fn quote_single(&self) -> OsString {
        let mut string = self.as_bytes().to_vec();
        let mut quote = "\'".as_bytes().to_vec();

        let mut quoted = vec![];
        quoted.append(&mut quote.clone());
        quoted.append(&mut string);
        quoted.append(&mut quote);

        OsString::from_vec(quoted)
    }

    fn splice_quoted(&self, from: &OsStr, to: Vec<OsString>) -> Vec<OsString> {
        let quoted_to = to.iter()
            .map(|to| to.quote())
            .collect();
        self.splice_with(from, quoted_to)
    }

    fn splice_quoted_single(&self, from: &OsStr, to: Vec<OsString>) -> Vec<OsString> {
        let quoted_to = to.iter()
            .map(|to| to.quote_single())
            .collect();
        self.splice_with(from, quoted_to)
    }

    fn splice_with(&self, from: &OsStr, to: Vec<OsString>) -> Vec<OsString> {
        let pos = self.position(from);

        if pos.is_none() {
            return vec![OsString::from(self)];
        }

        let pos = pos.unwrap();
        let string = self.as_bytes().to_vec();
        let from = from.as_bytes().to_vec();
        let fromlen = from.len();

        let lpart = OsString::from_vec(string[0..pos].to_vec());
        let rpart = OsString::from_vec(string[pos+fromlen..].to_vec());

        let mut result = vec![
            vec![lpart.trim_last_space()],
            to,
            vec![rpart]
        ].into_iter()
            .flatten()
            .filter(|part| part.len() != 0)
            .collect::<Vec<OsString>>();

        if result.last() == Some(&OsString::from("")) {
            result.pop();
            result
        } else { result }
    }

    fn replace(&self, from: &OsStr, to: &OsStr) -> OsString {
        let orig_string = self.as_bytes().to_vec();
        let from = from.as_bytes();
        let to = to.as_bytes().to_vec();
        let from_len = from.len();

        let new_string = orig_string
            .windows(from_len)
            .enumerate()
            .fold(Vec::new(), |mut pos, (i, chars)| {
                if chars == from {
                    pos.push(i);
                }
                pos
            }).iter().rev().fold(orig_string.to_vec(), |mut string, pos| {
                let pos = *pos;
                string.splice(pos..pos+from_len, to.clone());
                string
            });

        OsString::from_vec(new_string)
    }

    fn trim_last_space(&self) -> OsString {
        let string = self.as_bytes();
        let len = string.len();

        if len > 0 {
            OsString::from_vec(string[..len-1].to_vec())
        } else {
            self.to_os_string()
        }
    }

    fn trim_end_newlines(&self) -> &OsStr {
        let newline = OsString::from(
            String::from("\n")
        ).as_bytes()[0];

        let end_newline_pos = self.as_bytes()
            .iter()
            .enumerate()
            .rev()
            .fold(None, |pos, (i, ch)| {
                if ch != &newline && pos.is_none() {
                    Some(i+1)
                } else { pos }
            });

        match end_newline_pos {
            Some(pos) => {
                let substr = &self.as_bytes()[0..pos];
                OsStr::from_bytes(substr)
            }
            None => self
        }
    }

    fn contains_osstr(&self, pat: &OsStr) -> bool {
        let string = self.as_bytes();
        let pat = pat.as_bytes();
        let pat_len = pat.len();

        string.windows(pat_len)
            .find(|chars|
                  chars == &pat
            ).is_some()
    }

    fn position(&self, pat: &OsStr) -> Option<usize> {
        let string = self.as_bytes();
        let pat = pat.as_bytes();
        let pat_len = pat.len();

        string.windows(pat_len)
            .position(|chars|
                      chars == pat
            )
    }
}
