// Copyright 2019 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # Implemuntation of the functions in the ICU4C `ustring.h` header.
//!
//! This is where the UTF-8 strings get converted back and forth to the UChar
//! representation.
//!

use {
    rust_icu_sys as sys,
    std::{convert::TryFrom, string::FromUtf16Error},
};

/// The implementation of the ICU `UChar*`.
///
/// While the original type is defined in `umachine.h`, most useful functions for manipulating
/// `UChar*` are in fact here.
///
/// The first thing you probably want to do is to start from a UTF-8 rust string, produce a UChar.
/// This is necessarily done with a conversion.  See the `From` and `TryFrom` implementations
/// in this crate for that.
///
/// Implements `UChar*` from ICU.
#[derive(Debug, Clone)]
pub struct UChar {
    rep: Vec<sys::UChar>,
}

/// Same as `rust_icu_common::buffered_string_method_with_retry`, but for unicode strings.
///
/// Example use:
///
/// Declares an internal function `select_impl` with a templatized type signature, which is then
/// called in subsequent code.
///
/// ```rust ignore
/// pub fn select_ustring(&self, number: f64) -> Result<ustring::UChar, common::Error> {
///     const BUFFER_CAPACITY: usize = 20;
///     buffered_uchar_method_with_retry!(
///         select_impl,
///         BUFFER_CAPACITY,
///         [rep: *const sys::UPluralRules, number: f64,],
///         []
///     );
///
///     select_impl(
///         versioned_function!(uplrules_select),
///         self.rep.as_ptr(),
///         number,
///     )
/// }
/// ```
#[macro_export]
macro_rules! buffered_uchar_method_with_retry {

    ($method_name:ident, $buffer_capacity:expr,
     [$($before_arg:ident: $before_arg_type:ty,)*],
     [$($after_arg:ident: $after_arg_type:ty,)*]) => {
        fn $method_name(
            method_to_call: unsafe extern "C" fn(
                $($before_arg_type,)*
                *mut sys::UChar,
                i32,
                $($after_arg_type,)*
                *mut sys::UErrorCode,
            ) -> i32,
            $($before_arg: $before_arg_type,)*
            $($after_arg: $after_arg_type,)*
        ) -> Result<ustring::UChar, common::Error> {
            let mut status = common::Error::OK_CODE;
            let mut buf: Vec<sys::UChar> = vec![0; $buffer_capacity];

            // Requires that any pointers that are passed in are valid.
            let full_len: i32 = unsafe {
                assert!(common::Error::is_ok(status));
                method_to_call(
                    $($before_arg,)*
                    buf.as_mut_ptr() as *mut sys::UChar,
                    $buffer_capacity as i32,
                    $($after_arg,)*
                    &mut status,
                )
            };

            // ICU methods are inconsistent in whether they silently truncate the output or treat
            // the overflow as an error, so we need to check both cases.
            if status == sys::UErrorCode::U_BUFFER_OVERFLOW_ERROR ||
               (common::Error::is_ok(status) &&
                    full_len > $buffer_capacity
                        .try_into()
                        .map_err(|e| common::Error::wrapper(e))?) {

                assert!(full_len > 0);
                let full_len: usize = full_len
                    .try_into()
                    .map_err(|e| common::Error::wrapper(e))?;
                buf.resize(full_len, 0);

                // Same unsafe requirements as above, plus full_len must be exactly the output
                // buffer size.
                unsafe {
                    assert!(common::Error::is_ok(status));
                    method_to_call(
                        $($before_arg,)*
                        buf.as_mut_ptr() as *mut sys::UChar,
                        full_len as i32,
                        $($after_arg,)*
                        &mut status,
                    )
                };
            }

            common::Error::ok_or_warning(status)?;

            // Adjust the size of the buffer here.
            if (full_len >= 0) {
                let full_len: usize = full_len
                    .try_into()
                    .map_err(|e| common::Error::wrapper(e))?;
                buf.resize(full_len, 0);
            }
            Ok(ustring::UChar::from(buf))
        }
    }
}

impl From<&str> for UChar {
    /// Tries to produce a string from the UTF-8 encoded thing.
    ///
    /// Performs conversion in Rust rather than crossing FFI boundary to call `u_strFromUTF8`.
    fn from(s: &str) -> Self {
        Self {
            rep: s.encode_utf16().collect()
        }
    }
}

impl TryFrom<&UChar> for String {
    type Error = FromUtf16Error;

    /// Tries to produce a UTF-8 encoded rust string from a UChar.
    ///
    /// Attempts conversion in Rust rather than crossing the FFI boundary to call `u_strToUTF8`.
    fn try_from(u: &UChar) -> Result<String, Self::Error> {
        String::from_utf16(&u.rep[..])
    }
}

impl From<Vec<sys::UChar>> for UChar {
    /// Adopts a vector of [sys::UChar] into a string.
    fn from(rep: Vec<sys::UChar>) -> UChar {
        UChar { rep }
    }
}

impl UChar {
    /// Allocates a new UChar with given capacity.
    ///
    /// Capacity and size must always be the same with `UChar` when used for interacting with
    /// low-level code.
    pub fn new_with_capacity(capacity: usize) -> UChar {
        let rep: Vec<sys::UChar> = vec![0; capacity];
        UChar::from(rep)
    }

    /// Creates a new [UChar] from its low-level representation, a buffer
    /// pointer and a buffer size.
    ///
    /// Does *not* take ownership of the buffer that was passed in.
    ///
    /// **DO NOT USE UNLESS YOU HAVE NO OTHER CHOICE.**
    pub unsafe fn clone_from_raw_parts(rep: *mut sys::UChar, len: i32) -> UChar {
        assert!(len >= 0);
        // Always works for len: i32 >= 0.
        let cap = len as usize;

        // View the deconstructed buffer as a vector of UChars.  Then make a
        // copy of it to return.  This is not efficient, but is always safe.
        let original = Vec::from_raw_parts(rep, cap, cap);
        let copy = original.clone();
        // Don't free the buffer we don't own.
        std::mem::forget(original);
        UChar::from(copy)
    }

    /// Converts into a zeroed-out string.
    ///
    /// This is a very weird ICU API thing, where there apparently exists a zero-terminated
    /// `UChar*`.
    pub fn make_z(&mut self) {
        self.rep.push(0);
    }

    /// Returns the constant pointer to the underlying C representation.
    /// Intended for use in low-level code.
    pub fn as_c_ptr(&self) -> *const rust_icu_sys::UChar {
        self.rep.as_ptr()
    }

    /// Returns the length of the string, in code points.
    pub fn len(&self) -> usize {
        self.rep.len()
    }

    /// Returns the underlying representation as a mutable C representation.  Caller MUST ensure
    /// that the representation won't be reallocated as result of adding anything to it, and that
    /// it is correctly sized, or bad things will happen.
    pub fn as_mut_c_ptr(&mut self) -> *mut sys::UChar {
        self.rep.as_mut_ptr()
    }

    /// Resizes this string to match new_size.
    ///
    /// If the string is made longer, the new space is filled with zeroes.
    pub fn resize(&mut self, new_size: usize) {
        self.rep.resize(new_size, 0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trip_conversion() {
        let samples = vec!["", "Hello world!", "❤  Hello world  ❤"];
        for s in samples.iter() {
            let uchar = UChar::from(*s);
            let res =
                String::try_from(&uchar).expect(&format!("back conversion succeeds: {:?}", uchar));
            assert_eq!(*s, res);
        }
    }
}
