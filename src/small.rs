
use std::str;

const SMALL_BUFFER_LEN: usize = 8;

#[derive(Debug, Clone)]
pub struct SmallString {
    // The `buffer` and `length` fields are involved in unsafe mechanics.
    buffer: [u8; SMALL_BUFFER_LEN],
    length: usize,
}

impl SmallString {

    pub fn new(value: &str) -> Option<SmallString> {
        // The length must always be the full byte length to ensure the `unsafe` code
        // in `as_str` stays correct.
        let value = value.as_bytes();
        let length = value.len();
        if length <= SMALL_BUFFER_LEN {
            let mut buffer = [0; SMALL_BUFFER_LEN];
            buffer[..length].copy_from_slice(value);
            Some(SmallString { buffer, length })
        } else {
            None
        }
    }

    pub fn as_bytes(&self) -> &[u8] {
        // This must always return the full original slice to ensure the `unsafe` code
        // in `as_str` stays correct.
        &self.buffer[..self.length]
    }

    pub fn as_str(&self) -> &str {
        // This is safe because we created the byte slice from a valid `&str`.
        // While the the buffer storage may contain extra `0` values beyond the length
        // of the stored slice, `as_bytes` will always return a byteslice of the correct
        // length. Always use `as_bytes` and never use the buffer by itself.
        let bytes = self.as_bytes();
        unsafe { str::from_utf8_unchecked(bytes) }
    }
}

