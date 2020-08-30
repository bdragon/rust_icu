// Copyright 2020 Google LLC
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

//! # ICU word boundary analysis support for Rust

use {
    rust_icu_common::{self as common, simple_drop_impl},
    rust_icu_sys::{self as sys, *},
    rust_icu_ustring as ustring, rust_icu_utext as utext,
    std::{convert::TryFrom, ffi, os::raw, ptr},
};

/// Value returned to indicate that all text boundaries have been returned.
// UBRK_DONE is defined as a macro in ICU and macros are currently not supported
// by bindgen, so we define it ourselves here.
pub const UBRK_DONE: i32 = -1;

/// Rust wrapper for ICU `UBreakIterator` type.
#[derive(Debug)]
pub struct UBreakIterator {
    rep: ptr::NonNull<sys::UBreakIterator>,
}

simple_drop_impl!(UBreakIterator, ubrk_close);

impl Iterator for UBreakIterator {
    type Item = i32;

    /// Implements `ubrk_next`.
    fn next(&mut self) -> Option<Self::Item> {
        let index =
            unsafe { versioned_function!(ubrk_next)(self.rep.as_ptr()) };
        if index == UBRK_DONE {
            None
        } else {
            Some(index)
        }
    }
}

impl UBreakIterator {
    /// Implements `ubrk_open`.
    pub fn new(
        type_: sys::UBreakIteratorType,
        locale: &str,
        text: &str,
    ) -> Result<Self, common::Error> {
        let locale = ffi::CString::new(locale)?;
        let text = ustring::UChar::try_from(text)?;
        Self::new_ustring(type_, &locale, &text)
    }

    /// Implements `ubrk_open`.
    pub fn new_ustring(
        type_: sys::UBreakIteratorType,
        locale: &ffi::CString,
        text: &ustring::UChar,
    ) -> Result<Self, common::Error> {
        let mut status = common::Error::OK_CODE;
        let rep = unsafe {
            assert!(common::Error::is_ok(status));
            versioned_function!(ubrk_open)(
                type_,
                locale.as_ptr(),
                text.as_c_ptr(),
                text.len() as i32,
                &mut status,
            )
        };
        common::Error::ok_or_warning(status)?;
        assert_ne!(rep, 0 as *mut sys::UBreakIterator);
        Ok(Self {
            rep: ptr::NonNull::new(rep).unwrap(),
        })
    }

    /// Implements `ubrk_openRules`.
    pub fn new_rules(rules: &str, text: &str) -> Result<Self, common::Error> {
        let rules = ustring::UChar::try_from(rules)?;
        let text = ustring::UChar::try_from(text)?;
        Self::new_rules_ustring(&rules, &text)
    }

    /// Implements `ubrk_openRules`.
    pub fn new_rules_ustring(
        rules: &ustring::UChar,
        text: &ustring::UChar,
    ) -> Result<Self, common::Error> {
        let mut status = common::Error::OK_CODE;
        let mut parse_status = common::NO_PARSE_ERROR;
        let rep = unsafe {
            assert!(common::Error::is_ok(status));
            versioned_function!(ubrk_openRules)(
                rules.as_c_ptr(),
                rules.len() as i32,
                text.as_c_ptr(),
                text.len() as i32,
                &mut parse_status,
                &mut status,
            )
        };
        common::Error::ok_or_warning(status)?;
        common::parse_ok(parse_status)?;
        assert_ne!(rep, 0 as *mut sys::UBreakIterator);
        Ok(Self {
            rep: ptr::NonNull::new(rep).unwrap(),
        })
    }

    /// Implements `ubrk_openBinaryRules`.
    pub fn new_binary_rules(
        rules: &Vec<u8>,
        text: &str,
    ) -> Result<Self, common::Error> {
        let text = ustring::UChar::try_from(text)?;
        Self::new_binary_rules_ustring(rules, &text)
    }

    /// Implements `ubrk_openBinaryRules`.
    pub fn new_binary_rules_ustring(
        rules: &Vec<u8>,
        text: &ustring::UChar,
    ) -> Result<Self, common::Error> {
        let mut status = common::Error::OK_CODE;
        let rep = unsafe {
            assert!(common::Error::is_ok(status));
            versioned_function!(ubrk_openBinaryRules)(
                rules.as_ptr() as *const raw::c_uchar,
                rules.len() as i32,
                text.as_c_ptr(),
                text.len() as i32,
                &mut status,
            )
        };
        common::Error::ok_or_warning(status)?;
        assert_ne!(rep, 0 as *mut sys::UBreakIterator);
        Ok(Self {
            rep: ptr::NonNull::new(rep).unwrap(),
        })
    }

    /// Implements `ubrk_getBinaryRules`.
    pub fn get_binary_rules(&self) -> Result<Vec<u8>, common::Error> {
        let mut status = common::Error::OK_CODE;
        // Preflight to determine length of buffer for binary rules.
        let rules_len = unsafe {
            assert!(common::Error::is_ok(status));
            versioned_function!(ubrk_getBinaryRules)(
                self.rep.as_ptr(),
                0 as *mut raw::c_uchar,
                0,
                &mut status,
            )
        };
        common::Error::ok_preflight(status)?;
        let mut status = common::Error::OK_CODE;
        let mut rules = vec![0; rules_len as usize];
        unsafe {
            assert!(common::Error::is_ok(status));
            versioned_function!(ubrk_getBinaryRules)(
                self.rep.as_ptr(),
                rules.as_mut_ptr() as *mut raw::c_uchar,
                rules_len,
                &mut status,
            );
        }
        common::Error::ok_or_warning(status)?;
        Ok(rules)
    }

    /// Performs a thread-safe clone of the underlying representation. This is
    /// not achieved with a `Clone` trait implementation as the operation may fail.
    ///
    /// Implements `ubrk_safeClone`.
    pub fn safe_clone(&self) -> Result<Self, common::Error> {
        let mut status = common::Error::OK_CODE;
        let rep = unsafe {
            versioned_function!(ubrk_safeClone)(
                self.rep.as_ptr(),
                // The following two parameters, stackBuffer and pBufferSize,
                // are deprecated, so we pass NULL pointers.
                0 as *mut raw::c_void,
                0 as *mut i32,
                &mut status,
            )
        };
        common::Error::ok_or_warning(status)?;
        assert_ne!(rep, 0 as *mut sys::UBreakIterator);
        Ok(Self {
            rep: ptr::NonNull::new(rep).unwrap(),
        })
    }

    /// Implements `ubrk_setText`.
    pub fn set_text_ustring(
        &mut self,
        text: &ustring::UChar,
    ) -> Result<(), common::Error> {
        let mut status = common::Error::OK_CODE;
        unsafe {
            assert!(common::Error::is_ok(status));
            versioned_function!(ubrk_setText)(
                self.rep.as_ptr(),
                text.as_c_ptr(),
                text.len() as i32,
                &mut status,
            );
        }
        common::Error::ok_or_warning(status)?;
        Ok(())
    }

    /// Immplements `ubrk_setUText`.
    pub fn set_utext(&self, text: &mut utext::Text) -> Result<(), common::Error> {
        let mut status = common::Error::OK_CODE;
        unsafe {
            assert!(common::Error::is_ok(status));
            versioned_function!(ubrk_setUText)(
                self.rep.as_ptr(),
                text.as_mut_c_ptr(),
                &mut status,
            );
        }
        common::Error::ok_or_warning(status)
    }

    /// Implements `ubrk_first`.
    pub fn first(&self) -> i32 {
        unsafe { versioned_function!(ubrk_first)(self.rep.as_ptr()) }
    }

    /// Implements `ubrk_last`.
    pub fn last(&self) -> i32 {
        unsafe { versioned_function!(ubrk_last)(self.rep.as_ptr()) }
    }

    /// Implements `ubrk_preceding`.
    pub fn preceding(&self, offset: i32) -> i32 {
        unsafe {
            versioned_function!(ubrk_preceding)(self.rep.as_ptr(), offset)
        }
    }

    /// Implements `ubrk_following`.
    pub fn following(&self, offset: i32) -> i32 {
        unsafe {
            versioned_function!(ubrk_following)(self.rep.as_ptr(), offset)
        }
    }

    /// Implements `ubrk_isBoundary`.
    pub fn is_boundary(&self, offset: i32) -> bool {
        let result: sys::UBool = unsafe {
            versioned_function!(ubrk_isBoundary)(self.rep.as_ptr(), offset)
        };
        result != 0
    }

    /// Implements `ubrk_getRuleStatus`.
    pub fn get_rule_status(&self) -> i32 {
        unsafe { versioned_function!(ubrk_getRuleStatus)(self.rep.as_ptr()) }
    }

    /// Implements `ubrk_getRuleStatusVec`.
    pub fn get_rule_statuses(&self) -> Result<Vec<i32>, common::Error> {
        let mut status = common::Error::OK_CODE;
        let rules_len = unsafe {
            assert!(common::Error::is_ok(status));
            versioned_function!(ubrk_getRuleStatusVec)(
                self.rep.as_ptr(),
                0 as *mut i32,
                0,
                &mut status,
            )
        };
        common::Error::ok_preflight(status)?;
        let mut status = common::Error::OK_CODE;
        let mut rules: Vec<i32> = vec![0; rules_len as usize];
        unsafe {
            assert!(common::Error::is_ok(status));
            versioned_function!(ubrk_getRuleStatusVec)(
                self.rep.as_ptr(),
                rules.as_mut_ptr(),
                rules_len,
                &mut status,
            );
        }
        common::Error::ok_or_warning(status)?;
        Ok(rules)
    }
}

#[cfg(test)]
mod tests {
    use super::sys;
    use super::UBreakIterator;

    const TEXT: &str = r#""It wasn't the wine," murmured Mr. Snodgrass. \
    "It was the salmon.""#;

    #[test]
    fn test_binary_rules() {
        let mut iter =
            UBreakIterator::new(sys::UBreakIteratorType::UBRK_WORD, "en", TEXT)
                .unwrap();
        let breaks: Vec<i32> = iter.by_ref().collect();

        let bin_rules = iter.get_binary_rules().unwrap();

        let mut iter2 =
            UBreakIterator::new_binary_rules(&bin_rules, TEXT).unwrap();
        let breaks2: Vec<i32> = iter2.by_ref().collect();

        assert!(!breaks.is_empty());
        assert_eq!(breaks, breaks2);
    }
}
