// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Little Endian Base 128
//!
//! The LEB128 encoding is used throughout the networking code. This module provides utilities for
//! encoding/decoding this format.
//!
//! See https://en.wikipedia.org/wiki/LEB128

use core::{cmp, convert::TryFrom as _, fmt, mem, ops::Deref};

/// Returns an LEB128-encoded integer as a list of bytes.
///
/// This function accepts as parameter an `Into<u64>`. As such, one can also pass a `u8`, `u16`,
/// or `u32` for example. Use [`encode_usize`] for the `usize` equivalent.
///
/// # Example
///
/// ```
/// use substrate_lite::network::leb128;
///
/// assert_eq!(leb128::encode(0u64).collect::<Vec<_>>(), &[0]);
/// assert_eq!(
///     leb128::encode(0x123456789abcdefu64).collect::<Vec<_>>(),
///     &[239, 155, 175, 205, 248, 172, 209, 145, 1]
/// );
/// ```
pub fn encode(value: impl Into<u64>) -> impl ExactSizeIterator<Item = u8> + Clone {
    #[derive(Clone)]
    struct EncodeIter {
        value: u64,
        finished: bool,
    }

    impl Iterator for EncodeIter {
        type Item = u8;

        fn next(&mut self) -> Option<Self::Item> {
            if self.finished {
                return None;
            }

            if self.value < (1 << 7) {
                self.finished = true;
                return Some(u8::try_from(self.value).unwrap());
            }

            let ret = (1 << 7) | u8::try_from(self.value & 0b1111111).unwrap();
            self.value >>= 7;
            Some(ret)
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            let len = self.clone().count();
            (len, Some(len))
        }
    }

    impl ExactSizeIterator for EncodeIter {}

    EncodeIter {
        value: value.into(),
        finished: false,
    }
}

/// Returns an LEB128-encoded `usize` as a list of bytes.
///
/// See also [`encode`].
///
/// # Example
///
/// ```
/// use substrate_lite::network::leb128;
///
/// assert_eq!(leb128::encode_usize(0).collect::<Vec<_>>(), &[0]);
/// assert_eq!(
///     leb128::encode_usize(0x1234567).collect::<Vec<_>>(),
///     &[231, 138, 141, 9]
/// );
/// ```
pub fn encode_usize(value: usize) -> impl ExactSizeIterator<Item = u8> {
    encode(u64::try_from(value).unwrap())
}

// TODO: document all this below

pub struct Framed {
    max_len: usize,
    buffer: Vec<u8>,
    inner: FramedInner,
}

enum FramedInner {
    Length,
    Body { expected_len: usize },
}

impl Framed {
    pub fn new(max_len: usize) -> Self {
        Framed {
            max_len,
            buffer: Vec::with_capacity(max_len),
            inner: FramedInner::Length,
        }
    }

    pub fn take_frame(&mut self) -> Option<FrameDrain> {
        match self.inner {
            FramedInner::Body { expected_len } if expected_len == self.buffer.len() => {
                Some(FrameDrain(self))
            }
            _ => None,
        }
    }

    // TODO: corruption state after error returned?
    pub fn inject_data(&mut self, mut data: &[u8]) -> Result<usize, FramedError> {
        let mut total_read = 0;

        loop {
            match self.inner {
                FramedInner::Length => {
                    if data.is_empty() {
                        return Ok(total_read);
                    }

                    self.buffer.push(data[0]);
                    data = &data[1..];
                    total_read += 1;

                    if self.buffer.len() >= mem::size_of::<usize>() {
                        return Err(FramedError::LengthPrefixTooLarge);
                    }

                    if let Some(expected_len) = decode_leb128(&self.buffer) {
                        let expected_len = expected_len?;
                        if expected_len > self.max_len {
                            return Err(FramedError::LengthPrefixTooLarge);
                        }
                        self.buffer.clear();
                        self.inner = FramedInner::Body { expected_len };
                    }
                }
                FramedInner::Body { expected_len } => {
                    debug_assert!(self.buffer.len() <= expected_len);
                    let missing = expected_len - self.buffer.len();
                    let available = cmp::min(missing, data.len());
                    self.buffer.extend_from_slice(&data[..available]);
                    debug_assert!(self.buffer.len() <= expected_len);
                    total_read += available;
                    return Ok(total_read);
                }
            }
        }
    }
}

fn decode_leb128(buffer: &[u8]) -> Option<Result<usize, FramedError>> {
    let mut out = 0usize;

    for (n, byte) in buffer.iter().enumerate() {
        match usize::from(*byte & 0b1111111).checked_mul(1 << (7 * n)) {
            Some(o) => out |= o,
            None => return Some(Err(FramedError::LengthPrefixTooLarge)),
        };

        if (*byte & 0x80) == 0 {
            assert_eq!(n, buffer.len() - 1);
            return Some(Ok(out));
        }
    }

    None
}

#[derive(Debug, derive_more::Display)]
pub enum FramedError {
    LengthPrefixTooLarge,
}

pub struct FrameDrain<'a>(&'a mut Framed);

impl<'a> FrameDrain<'a> {
    pub fn into_vec(self) -> Vec<u8> {
        mem::replace(&mut self.0.buffer, Vec::new())
    }
}

impl<'a> Deref for FrameDrain<'a> {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        &self.0.buffer
    }
}

impl<'a> AsRef<[u8]> for FrameDrain<'a> {
    fn as_ref(&self) -> &[u8] {
        &self.0.buffer
    }
}

impl<'a> From<FrameDrain<'a>> for Vec<u8> {
    fn from(drain: FrameDrain<'a>) -> Vec<u8> {
        drain.into_vec()
    }
}

impl<'a> fmt::Debug for FrameDrain<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0.buffer, f)
    }
}

impl<'a> Drop for FrameDrain<'a> {
    fn drop(&mut self) {
        debug_assert!(matches!(self.0.inner, FramedInner::Body { .. }));
        self.0.buffer.clear();
        self.0.inner = FramedInner::Length;
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn basic_encode() {
        let obtained = super::encode(0x123456789abcdefu64).collect::<Vec<_>>();
        assert_eq!(obtained, &[239, 155, 175, 205, 248, 172, 209, 145, 1]);
    }

    #[test]
    fn encode_zero() {
        let obtained = super::encode(0u64).collect::<Vec<_>>();
        assert_eq!(obtained, &[0x0u8]);
    }

    #[test]
    fn exact_size_iterator() {
        for _ in 0..128 {
            let iter = super::encode(rand::random::<u64>());
            let expected = iter.len();
            let obtained = iter.count();
            assert_eq!(expected, obtained);
        }
    }

    // TODO: more tests
}