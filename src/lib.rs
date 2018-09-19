#![warn(
    missing_debug_implementations,
    missing_docs,
)]
//! Distinction, validation and optimized storage for text values.
//!
//! # Features
//!
//! * Specialized storage for `&'static str` values.
//! * Small string storage for values below a certain length.
//! * Shared, thread-safe storage for longer, non-static values.
//! * Main `Text<K>` type where `K` is a `Kind` identifying a kind of text.
//! * Reusable `Check` constraints associated with `Kind` types via `Kind::Check`.
//! * Cheap `&Text<Source>` to `&Text<Target>` conversions.
//! * The `Error` type attaches the `Kind::NAME` to the beginning of the error chain.
//! * Optional `serde` support with the `serde` feature.
//!
//! # Unconstrained Values
//!
//! The predefined `check::Any` constraint can be used for `Kind` types that don't
//! have any constraints and accept all kinds of values.
//!
//! When the `check::Any` constraint is used, some additional functions on `Text`
//! are available that allow avoiding unnecessary error handling.
//!
//! This means that the `check::Any` constraint should not be used for prototyping,
//! since a switch to a different constraint later will restrict the available
//! interface.
//!
//! # Examples
//!
//! Simple title types with a common constraint.
//!
//! ```
//! // The kinds of errors that might happen.
//! #[derive(Debug, PartialEq, Eq)]
//! enum TitleError {
//!     Empty,
//!     LeadingWhitespace,
//!     TrailingWhitespace,
//! }
//!
//! // Our title constraint type.
//! // It will never be instantiated, so it doesn't have state.
//! struct TitleCheck;
//!
//! // Turning our constraint type into a checkable constraint.
//! impl txk::Check for TitleCheck {
//!
//!     // Setting the constraint's error type
//!     type Error = TitleError;
//!
//!     // Implementing our constraint check.
//!     fn check(value: &str) -> Result<(), Self::Error> {
//!         if value.is_empty() {
//!             Err(TitleError::Empty)
//!         } else if value.starts_with(char::is_whitespace) {
//!             Err(TitleError::LeadingWhitespace)
//!         } else if value.ends_with(char::is_whitespace) {
//!             Err(TitleError::TrailingWhitespace)
//!         } else {
//!             Ok(())
//!         }
//!     }
//! }
//!
//! // A title for a full document.
//! // It will never be instantiated, so it doesn't have state.
//! struct DocumentTitle;
//!
//! // Turn the kind into a type usable by `Text`.
//! impl txk::Kind for DocumentTitle {
//!
//!     // Use the title constraint we declared above.
//!     type Check = TitleCheck;
//!
//!     // Give the kind a name for error messages.
//!     const NAME: &'static str = "document title";
//! }
//!
//! // A title for a single section.
//! struct SectionTitle;
//!
//! // Turn the section title type into a kind.
//! // This is very similar to DocumentTitle, except for
//! // the `NAME`.
//! impl txk::Kind for SectionTitle {
//!
//!     // Use the same check as `DocumentTitle`.
//!     type Check = TitleCheck;
//!
//!     // The only thing that is different: The kind
//!     // gets a different name.
//!     const NAME: &'static str = "section title";
//! }
//!
//! // Values will have to pass the constraint check.
//! assert_eq!(
//!     txk::Text::<DocumentTitle>::new(""),
//!     Err(txk::Error::new(TitleError::Empty)),
//! );
//! assert_eq!(
//!     txk::Text::<DocumentTitle>::new("  foo"),
//!     Err(txk::Error::new(TitleError::LeadingWhitespace)),
//! );
//! assert_eq!(
//!     txk::Text::<SectionTitle>::new("foo  "),
//!     Err(txk::Error::new(TitleError::TrailingWhitespace)),
//! );
//!
//! // Construction with a valid value.
//! let section_title: txk::Text<SectionTitle> =
//!     txk::Text::new("Test Title")
//!     .expect("passes all constraint checks");
//!
//! // Since they share the same constraint, we can convert
//! // them without validating. Different types will have to
//! // use a validating conversion function instead.
//! let doc_title: txk::Text<DocumentTitle> =
//!     section_title.to_other();
//!
//! // We can also convert without needing a new owned value.
//! let doc_title_ref: &txk::Text<SectionTitle> =
//!     section_title.as_other();
//!
//! assert_eq!(&section_title, &doc_title);
//! assert_eq!(&section_title, doc_title_ref);
//! ```

#[cfg(feature = "serde")]
extern crate serde;

#[macro_use]
extern crate static_assertions;

// Small string storage logic.
mod small;

// Infrastructure traits, mainly `Kind` and `Check`.
mod traits;
pub use self::traits::{Kind, Check};

// Error types and trait implementations. We only need the base error type.
mod errors;
pub use self::errors::{Error};

// Publicly available preset check types.
pub mod check;

#[cfg(feature = "serde")]
mod feature_serde;

use std::borrow;
use std::cmp;
use std::fmt;
use std::hash;
use std::marker;
use std::ops;
use std::str;
use std::sync;

#[derive(Debug, Clone)]
enum Storage {
    Small(small::SmallString),
    Static(&'static str),
    Dynamic(sync::Arc<str>),
}

impl Storage {

    fn as_str(&self) -> &str {
        match *self {
            Storage::Small(ref value) => value.as_str(),
            Storage::Static(value) => value,
            Storage::Dynamic(ref value) => value,
        }
    }

    fn as_bytes(&self) -> &[u8] {
        self.as_str().as_bytes()
    }
}

/// A text value of a specific kind.
///
/// The type parameter `K` specifies the `Kind` of text that is stored. The `Kind`
/// has an attached `Check` type that implements the type constraint.
///
/// # Storage
///
/// If a value is constructed with one of the `*_from_static` functions, it will
/// be stored as a reference with static lifetime. The static reference can be
/// queried with `as_static_str`.
///
/// If the byte length of a non-static value is below a certain limit, the data will be
/// stored inline and not in a dynamic allocation.
///
/// Longer non-static values are stored in a dynamically allocated, shared, thread-safe
/// storage.
///
/// # Errors
///
/// The `Check` types provide associated `Check::Error` types giving validation
/// failure information.
///
/// The functions operating on `Text` wrap the `Check::Error` values in the
/// `Error` type, which adds `Kind::NAME` output to the beginning of the error
/// chain.
#[repr(transparent)] // Ensure a stable struct layout.
pub struct Text<K> {
    // This type unsafely implements `Send` and `Sync`, assuming that the `Storage`
    // is always threadsafe. Care must be taken when changing this structure to make
    // sure it doesn't contain non-threadsafe elements.
    storage: Storage,
    _kind: marker::PhantomData<*const K>, // `*const` to indicate no ownership
}

// These are safe because the `Storage` implements `Send` and `Sync`. Automatically
// deriving these makes them dependent on the `K` type parameter, which is a phantom
// and does not carry data.
assert_impl!(test_storage_send_sync; Storage, Send, Sync);
unsafe impl<K> Send for Text<K> {}
unsafe impl<K> Sync for Text<K> {}

/// Validated constructors.
///
/// These constructors work for all kinds of `Text` values. Handling validation
/// errors is mandatory.
impl<K> Text<K>
where
    K: Kind,
{
    /// Attempt to construct a validated value.
    ///
    /// Small values will be stored inline instead of using a shared
    /// allocated storage.
    ///
    /// # Errors
    ///
    /// This constructor returns an error when the given value does not
    /// pass the `Kind::Check` constraint.
    ///
    /// # Examples
    ///
    /// ```
    /// #[derive(Debug)]
    /// struct NotEmptyError;
    ///
    /// struct NotEmptyCheck;
    /// impl txk::Check for NotEmptyCheck {
    ///     type Error = NotEmptyError;
    ///     fn check(value: &str) -> Result<(), Self::Error> {
    ///         if !value.is_empty() { Ok(()) }
    ///         else { Err(NotEmptyError) }
    ///     }
    /// }
    ///
    /// struct MyKind;
    /// impl txk::Kind for MyKind {
    ///     type Check = NotEmptyCheck;
    ///     const NAME: &'static str = "my kind";
    /// }
    ///
    /// let value: txk::Text<MyKind> = txk::Text::new("foo")
    ///     .expect("value isn't empty");
    ///
    /// assert_eq!(value, "foo");
    /// ```
    pub fn new<T>(value: T) -> Result<Text<K>, Error<K>>
    where
        T: AsRef<str>,
    {
        let value = value.as_ref();
        K::Check::check(value).map_err(Error::new)?;
        Ok(Text {
            storage: small::SmallString::new(value)
                .map(Storage::Small)
                .unwrap_or_else(|| Storage::Dynamic(value.into())),
            _kind: marker::PhantomData,
        })
    }

    /// Attempt to construct a validated value from a `&'static str`.
    ///
    /// This will use a `'static` specific storage option that will not
    /// require an allocation.
    ///
    /// You can use `as_static_str` to retrieve the `&'static str`.
    ///
    /// # Errors
    ///
    /// This constructor returns an error when the given value does not
    /// pass the `Kind::Check` constraint.
    ///
    /// # Examples
    ///
    /// ```
    /// #[derive(Debug)]
    /// struct NotEmptyError;
    ///
    /// struct NotEmptyCheck;
    /// impl txk::Check for NotEmptyCheck {
    ///     type Error = NotEmptyError;
    ///     fn check(value: &str) -> Result<(), Self::Error> {
    ///         if !value.is_empty() { Ok(()) }
    ///         else { Err(NotEmptyError) }
    ///     }
    /// }
    ///
    /// struct MyKind;
    /// impl txk::Kind for MyKind {
    ///     type Check = NotEmptyCheck;
    ///     const NAME: &'static str = "my kind";
    /// }
    ///
    /// let value: txk::Text<MyKind> = txk::Text::new_from_static("foo")
    ///     .expect("value isn't empty");
    ///
    /// assert_eq!(value, "foo");
    /// assert_eq!(value.as_static_str(), Some("foo"));
    /// ```
    pub fn new_from_static(value: &'static str) -> Result<Text<K>, Error<K>> {
        K::Check::check(value).map_err(Error::new)?;
        Ok(Text {
            storage: Storage::Static(value),
            _kind: marker::PhantomData,
        })
    }
}

/// Convenience onstructors for `Kind` types with a `check::Any` constraint.
///
/// Since `check::Any` accepts any value a validation step is not required and
/// there are no errors to handle.
impl<K> Text<K>
where
    K: Kind<Check = check::Any>,
{
    /// Construct a value for a `Kind` with a `check::Any` constraint.
    ///
    /// Since `check::Any` accepts any value a validation step is not required and
    /// there are no errors to handle.
    ///
    /// Small values will be stored inline instead of using a shared
    /// allocated storage.
    ///
    /// # Examples
    ///
    /// ```
    /// struct MyKind;
    /// impl txk::Kind for MyKind {
    ///     type Check = txk::check::Any;
    ///     const NAME: &'static str = "my kind";
    /// }
    ///
    /// let value: txk::Text<MyKind> = txk::Text::new_any("foo");
    ///
    /// assert_eq!(value, "foo");
    /// ```
    pub fn new_any<T>(value: T) -> Text<K>
    where
        T: AsRef<str>,
    {
        let value = value.as_ref();
        Text {
            storage: small::SmallString::new(value)
                .map(Storage::Small)
                .unwrap_or_else(|| Storage::Dynamic(value.into())),
            _kind: marker::PhantomData,
        }
    }

    /// Construct a value for a `Kind` with a `check::Any` constraint from
    /// a `&'static str`.
    ///
    /// Since `check::Any` accepts any value a validation step is not required and
    /// there are no errors to handle.
    ///
    /// This will use a `'static` specific storage option that will not
    /// require an allocation.
    ///
    /// You can use `as_static_str` to retrieve the `&'static str`.
    ///
    /// # Examples
    ///
    /// ```
    /// struct MyKind;
    /// impl txk::Kind for MyKind {
    ///     type Check = txk::check::Any;
    ///     const NAME: &'static str = "my kind";
    /// }
    ///
    /// let value: txk::Text<MyKind> =
    ///     txk::Text::new_any_from_static("foo");
    ///
    /// assert_eq!(value, "foo");
    /// assert_eq!(value.as_static_str(), Some("foo"));
    /// ```
    pub fn new_any_from_static(value: &'static str) -> Text<K> {
        Text {
            storage: Storage::Static(value),
            _kind: marker::PhantomData,
        }
    }
}

/// Conversions to other owned `Text` kinds.
impl<K> Text<K>
where
    K: Kind,
{
    /// Convert to a different `Kind` with the same `Kind::Check` while keeping ownership
    /// of the original.
    ///
    /// Since both kinds have the same `Kind::Check`, validation can be omitted and there
    /// are no errors to handle with this conversion.
    ///
    /// If the value is in shared dynamic storage an atomic counter update will occur.
    ///
    /// # Examples
    ///
    /// ```
    /// #[derive(Debug)]
    /// struct NotEmptyError;
    ///
    /// struct NotEmptyCheck;
    /// impl txk::Check for NotEmptyCheck {
    ///     type Error = NotEmptyError;
    ///     fn check(value: &str) -> Result<(), Self::Error> {
    ///         if !value.is_empty() { Ok(()) }
    ///         else { Err(NotEmptyError) }
    ///     }
    /// }
    ///
    /// struct KindA;
    /// impl txk::Kind for KindA {
    ///     type Check = NotEmptyCheck;
    ///     const NAME: &'static str = "kind A";
    /// }
    ///
    /// struct KindB;
    /// impl txk::Kind for KindB {
    ///     type Check = NotEmptyCheck;
    ///     const NAME: &'static str = "kind B";
    /// }
    ///
    /// let a: txk::Text<KindA> = txk::Text::new("foo")
    ///     .expect("value isn't empty");
    /// let b: txk::Text<KindB> = a.to_other();
    ///
    /// assert_eq!(a, b);
    /// ```
    pub fn to_other<K2>(&self) -> Text<K2>
    where
        K2: Kind<Check = K::Check>,
    {
        Text {
            storage: self.storage.clone(),
            _kind: marker::PhantomData,
        }
    }

    /// Convert to a different `Kind` with the same `Kind::Check` and give up ownership.
    ///
    /// Since both kinds have the same `Kind::Check`, validation can be omitted and there
    /// are no errors to handle with this conversion.
    ///
    /// This operation does not cause an atomic counter update in any case, due to the
    /// storage being reused in the target value.
    ///
    /// # Examples
    ///
    /// ```
    /// #[derive(Debug)]
    /// struct NotEmptyError;
    ///
    /// struct NotEmptyCheck;
    /// impl txk::Check for NotEmptyCheck {
    ///     type Error = NotEmptyError;
    ///     fn check(value: &str) -> Result<(), Self::Error> {
    ///         if !value.is_empty() { Ok(()) }
    ///         else { Err(NotEmptyError) }
    ///     }
    /// }
    ///
    /// struct KindA;
    /// impl txk::Kind for KindA {
    ///     type Check = NotEmptyCheck;
    ///     const NAME: &'static str = "kind A";
    /// }
    ///
    /// struct KindB;
    /// impl txk::Kind for KindB {
    ///     type Check = NotEmptyCheck;
    ///     const NAME: &'static str = "kind B";
    /// }
    ///
    /// let a: txk::Text<KindA> = txk::Text::new("foo")
    ///     .expect("value isn't empty");
    /// let b: txk::Text<KindB> = a.into_other();
    ///
    /// assert_eq!(b, "foo");
    /// ```
    pub fn into_other<K2>(self) -> Text<K2>
    where
        K2: Kind<Check = K::Check>,
    {
        Text {
            storage: self.storage,
            _kind: marker::PhantomData,
        }
    }

    /// Attempt to convert to a different `Kind` with a different `Kind::Check` constraint
    /// while keeping ownership of the original.
    ///
    /// If the value is in shared dynamic storage an atomic counter update will occur.
    ///
    /// # Errors
    ///
    /// This conversion function returns an error when the stored value does not pass
    /// the target `Kind::Check` constraint.
    ///
    /// # Examples
    ///
    /// ```
    /// struct KindA;
    /// impl txk::Kind for KindA {
    ///     type Check = txk::check::Any;
    ///     const NAME: &'static str = "kind A";
    /// }
    ///
    /// #[derive(Debug)]
    /// struct NotEmptyError;
    ///
    /// struct NotEmptyCheck;
    /// impl txk::Check for NotEmptyCheck {
    ///     type Error = NotEmptyError;
    ///     fn check(value: &str) -> Result<(), Self::Error> {
    ///         if !value.is_empty() { Ok(()) }
    ///         else { Err(NotEmptyError) }
    ///     }
    /// }
    ///
    /// struct KindB;
    /// impl txk::Kind for KindB {
    ///     type Check = NotEmptyCheck;
    ///     const NAME: &'static str = "kind B";
    /// }
    ///
    /// let a: txk::Text<KindA> = txk::Text::new("foo")
    ///     .expect("value passes all-accepting Any constraint");
    /// let b: txk::Text<KindB> = a.try_to_other()
    ///     .expect("value can be KindB since it's not empty");
    ///
    /// assert_eq!(a, b);
    /// ```
    pub fn try_to_other<K2>(&self) -> Result<Text<K2>, Error<K2>>
    where
        K2: Kind,
    {
        K2::Check::check(&self).map_err(Error::new)?;
        Ok(Text {
            storage: self.storage.clone(),
            _kind: marker::PhantomData,
        })
    }

    /// Convert to a different `Kind` with a `check::Any` constraint while keeping
    /// ownership of the original.
    ///
    /// Since `check::Any` accepts any value a validation step is not required and
    /// there are no errors to handle.
    ///
    /// If the value is in shared dynamic storage an atomic counter update will occur.
    ///
    /// # Examples
    ///
    /// ```
    /// #[derive(Debug)]
    /// struct NotEmptyError;
    ///
    /// struct NotEmptyCheck;
    /// impl txk::Check for NotEmptyCheck {
    ///     type Error = NotEmptyError;
    ///     fn check(value: &str) -> Result<(), Self::Error> {
    ///         if !value.is_empty() { Ok(()) }
    ///         else { Err(NotEmptyError) }
    ///     }
    /// }
    ///
    /// struct KindA;
    /// impl txk::Kind for KindA {
    ///     type Check = NotEmptyCheck;
    ///     const NAME: &'static str = "kind A";
    /// }
    ///
    /// struct KindB;
    /// impl txk::Kind for KindB {
    ///     type Check = txk::check::Any;
    ///     const NAME: &'static str = "kind B";
    /// }
    ///
    /// let a: txk::Text<KindA> = txk::Text::new("foo")
    ///     .expect("value isn't empty");
    /// let b: txk::Text<KindB> = a.to_any();
    ///
    /// assert_eq!(a, b);
    /// ```
    pub fn to_any<K2>(&self) -> Text<K2>
    where
        K2: Kind<Check = check::Any>,
    {
        Text {
            storage: self.storage.clone(),
            _kind: marker::PhantomData,
        }
    }

    /// Convert to a different `Kind` with a `check::Any` constraint and give up ownership.
    ///
    /// Since `check::Any` accepts any value a validation step is not required and
    /// there are no errors to handle.
    ///
    /// This operation does not cause an atomic counter update in any case, due to the
    /// storage being reused in the target value.
    ///
    /// # Examples
    ///
    /// ```
    /// #[derive(Debug)]
    /// struct NotEmptyError;
    ///
    /// struct NotEmptyCheck;
    /// impl txk::Check for NotEmptyCheck {
    ///     type Error = NotEmptyError;
    ///     fn check(value: &str) -> Result<(), Self::Error> {
    ///         if !value.is_empty() { Ok(()) }
    ///         else { Err(NotEmptyError) }
    ///     }
    /// }
    ///
    /// struct KindA;
    /// impl txk::Kind for KindA {
    ///     type Check = NotEmptyCheck;
    ///     const NAME: &'static str = "kind A";
    /// }
    ///
    /// struct KindB;
    /// impl txk::Kind for KindB {
    ///     type Check = txk::check::Any;
    ///     const NAME: &'static str = "kind B";
    /// }
    ///
    /// let a: txk::Text<KindA> = txk::Text::new("foo")
    ///     .expect("value isn't empty");
    /// let b: txk::Text<KindB> = a.into_any();
    ///
    /// assert_eq!(b, "foo");
    /// ```
    pub fn into_any<K2>(self) -> Text<K2>
    where
        K2: Kind<Check = check::Any>,
    {
        Text {
            storage: self.storage,
            _kind: marker::PhantomData,
        }
    }
}

// Turn the `&Text<K>` into a `&Text<K2>` via *const _ pointers.
// It is crucial that `Text<K>` and `Text<K2>` always have the same layout for this to
// work. It is assumed this is the case because `K` is a ZST phantom type, not changing
// the storage, and the `Text` struct has a `C` layout.
unsafe fn transmute_kind<K1, K2>(source: &Text<K1>) -> &Text<K2>
where
    K1: Kind,
    K2: Kind,
{
    // This makes sure that `Storage` and different kinds of `Text` types all have the same
    // size. This is required for the safety of conversions into references of other kinds.
    assert_eq_size!(Text<K1>, Text<K2>);
    assert_eq_size!(Text<K1>, Storage);
    assert_eq_size!(Text<K1>, Text<()>);
    assert_eq_size!(Text<K1>, Text<String>);

    let target_ptr =
        source
        as *const Text<K1>
        as *const Text<K2>;
    let target_ref = &*target_ptr;

    target_ref
}

/// Conversions to references of other `Text` kinds.
impl<K> Text<K>
where
    K: Kind,
{
    // This implementation block contains encapsulated unsafe conversions to other kind
    // references. It is crucial that `Text<K>` and `Text<K2>` always have the same layout
    // for this to work.

    /// Convert into a reference of another `Kind` with the same `Kind::Check`.
    ///
    /// # Examples
    ///
    /// ```
    /// #[derive(Debug)]
    /// struct NotEmptyError;
    ///
    /// struct NotEmptyCheck;
    /// impl txk::Check for NotEmptyCheck {
    ///     type Error = NotEmptyError;
    ///     fn check(value: &str) -> Result<(), Self::Error> {
    ///         if !value.is_empty() { Ok(()) }
    ///         else { Err(NotEmptyError) }
    ///     }
    /// }
    ///
    /// struct KindA;
    /// impl txk::Kind for KindA {
    ///     type Check = NotEmptyCheck;
    ///     const NAME: &'static str = "kind A";
    /// }
    ///
    /// struct KindB;
    /// impl txk::Kind for KindB {
    ///     type Check = NotEmptyCheck;
    ///     const NAME: &'static str = "kind B";
    /// }
    ///
    /// let a: txk::Text<KindA> = txk::Text::new("foo")
    ///     .expect("value isn't empty");
    /// let b: &txk::Text<KindB> = a.as_other();
    ///
    /// assert_eq!(&a, b);
    /// ```
    pub fn as_other<K2>(&self) -> &Text<K2>
    where
        K2: Kind<Check = K::Check>,
    {
        // See the comment one level up and the in-code documentation for `transmute_kind`
        // for why this is considered safe.
        let target_ref: &Text<K2> = unsafe { transmute_kind(self) };

        target_ref
    }

    /// Attempt to convert into a reference of another `Kind`.
    ///
    /// # Errors
    ///
    /// This conversion function returns an error when the stored value does not pass
    /// the target `Kind::Check` constraint.
    ///
    /// # Examples
    ///
    /// ```
    /// struct KindA;
    /// impl txk::Kind for KindA {
    ///     type Check = txk::check::Any;
    ///     const NAME: &'static str = "kind A";
    /// }
    ///
    /// #[derive(Debug)]
    /// struct NotEmptyError;
    ///
    /// struct NotEmptyCheck;
    /// impl txk::Check for NotEmptyCheck {
    ///     type Error = NotEmptyError;
    ///     fn check(value: &str) -> Result<(), Self::Error> {
    ///         if !value.is_empty() { Ok(()) }
    ///         else { Err(NotEmptyError) }
    ///     }
    /// }
    ///
    /// struct KindB;
    /// impl txk::Kind for KindB {
    ///     type Check = NotEmptyCheck;
    ///     const NAME: &'static str = "kind B";
    /// }
    ///
    /// let a: txk::Text<KindA> = txk::Text::new("foo")
    ///     .expect("value passes all-accepting Any constraint");
    /// let b: &txk::Text<KindB> = a.try_as_other()
    ///     .expect("value can be KindB since it's not empty");
    ///
    /// assert_eq!(&a, b);
    /// ```
    pub fn try_as_other<K2>(&self) -> Result<&Text<K2>, Error<K2>>
    where
        K2: Kind,
    {
        K2::Check::check(&self).map_err(Error::new)?;

        // See the comment one level up and the in-code documentation for `transmute_kind`
        // for why this is considered safe.
        let target_ref: &Text<K2> = unsafe { transmute_kind(self) };

        Ok(target_ref)
    }

    /// Convert into a reference of another `Kind` with a `check::Any` constraint.
    ///
    /// Since `check::Any` accepts any value a validation step is not required and
    /// there are no errors to handle.
    ///
    /// # Examples
    ///
    /// ```
    /// #[derive(Debug)]
    /// struct NotEmptyError;
    ///
    /// struct NotEmptyCheck;
    /// impl txk::Check for NotEmptyCheck {
    ///     type Error = NotEmptyError;
    ///     fn check(value: &str) -> Result<(), Self::Error> {
    ///         if !value.is_empty() { Ok(()) }
    ///         else { Err(NotEmptyError) }
    ///     }
    /// }
    ///
    /// struct KindA;
    /// impl txk::Kind for KindA {
    ///     type Check = NotEmptyCheck;
    ///     const NAME: &'static str = "kind A";
    /// }
    ///
    /// struct KindB;
    /// impl txk::Kind for KindB {
    ///     type Check = txk::check::Any;
    ///     const NAME: &'static str = "kind B";
    /// }
    ///
    /// let a: txk::Text<KindA> = txk::Text::new("foo")
    ///     .expect("value isn't empty");
    /// let b: &txk::Text<KindB> = a.as_any();
    ///
    /// assert_eq!(&a, b);
    /// ```
    pub fn as_any<K2>(&self) -> &Text<K2>
    where
        K2: Kind<Check = check::Any>,
    {
        // See the comment one level up and the in-code documentation for `transmute_kind`
        // for why this is considered safe.
        let target_ref: &Text<K2> = unsafe { transmute_kind(self) };

        target_ref
    }
}

/// Conversions to non-`Text` values.
impl<K> Text<K> {

    /// Retrieve a string slice from the stored data.
    ///
    /// # Examples
    ///
    /// ```
    /// struct MyKind;
    /// impl txk::Kind for MyKind {
    ///     type Check = txk::check::Any;
    ///     const NAME: &'static str = "my kind";
    /// }
    ///
    /// let value: txk::Text<MyKind> = txk::Text::new_any("foo");
    ///
    /// assert_eq!(value.as_str(), "foo");
    /// ```
    pub fn as_str(&self) -> &str {
        self.storage.as_str()
    }

    /// Attempt to retrieve a `&'static str` from the stored data.
    ///
    /// This will only return a value if the `Text` was originally constructed
    /// with one of the `*_from_static` functions.
    ///
    /// # Examples
    ///
    /// ```
    /// struct MyKind;
    /// impl txk::Kind for MyKind {
    ///     type Check = txk::check::Any;
    ///     const NAME: &'static str = "my kind";
    /// }
    ///
    /// // Using the `&'static str` constructor.
    /// let value: txk::Text<MyKind> =
    ///     txk::Text::new_any_from_static("foo");
    /// assert_eq!(value.as_static_str(), Some("foo"));
    ///
    /// // Using the general constructor.
    /// let value: txk::Text<MyKind> =
    ///     txk::Text::new_any("foo");
    /// assert_eq!(value.as_static_str(), None);
    /// ```
    pub fn as_static_str(&self) -> Option<&'static str> {
        match self.storage {
            Storage::Static(value) => Some(value),
            _ => None,
        }
    }

    /// Retrieve a byte slice from the stored data.
    ///
    /// # Examples
    ///
    /// ```
    /// struct MyKind;
    /// impl txk::Kind for MyKind {
    ///     type Check = txk::check::Any;
    ///     const NAME: &'static str = "my kind";
    /// }
    ///
    /// let value: txk::Text<MyKind> = txk::Text::new_any("foo");
    ///
    /// assert_eq!(value.as_bytes(), "foo".as_bytes());
    /// ```
    pub fn as_bytes(&self) -> &[u8] {
        self.storage.as_bytes()
    }
}

impl<K> ops::Deref for Text<K> {

    type Target = str;

    fn deref(&self) -> &str {
        self.storage.as_str()
    }
}

impl<K> str::FromStr for Text<K>
where
    K: Kind,
{
    type Err = Error<K>;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        Text::new(value)
    }
}

impl<K> AsRef<str> for Text<K> {

    fn as_ref(&self) -> &str {
        self.storage.as_str()
    }
}

impl<K> AsRef<[u8]> for Text<K> {

    fn as_ref(&self) -> &[u8] {
        self.storage.as_bytes()
    }
}

impl<K> hash::Hash for Text<K> {

    fn hash<H>(&self, state: &mut H)
    where
        H: hash::Hasher,
    {
        self.as_str().hash(state);
    }
}

impl<K, T> cmp::PartialEq<T> for Text<K>
where
    T: AsRef<str>,
{
    fn eq(&self, other: &T) -> bool {
        self.as_str().eq(other.as_ref())
    }
}

impl<K> cmp::Eq for Text<K> {}

impl<K, T> cmp::PartialOrd<T> for Text<K>
where
    T: AsRef<str>,
{
    fn partial_cmp(&self, other: &T) -> Option<cmp::Ordering> {
        self.as_str().partial_cmp(other.as_ref())
    }
}

impl<K> cmp::Ord for Text<K> {

    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl<K> borrow::Borrow<str> for Text<K> {

    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl<K> Clone for Text<K> {

    fn clone(&self) -> Self {
        Text {
            storage: self.storage.clone(),
            _kind: marker::PhantomData,
        }
    }
}

impl<K> fmt::Debug for Text<K> {

    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("Text").field("storage", &self.storage).finish()
    }
}

impl<K> fmt::Display for Text<K> {
    
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self.storage.as_str(), fmt)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestAnyKind;

    impl Kind for TestAnyKind {

        type Check = check::Any;

        const NAME: &'static str = "TestAny";
    }

    type TestAny = Text<TestAnyKind>;

    #[test]
    fn storage_static() {

        let text = TestAny::new_from_static("foo").unwrap();
        match text {
            Text { storage: Storage::Static(val), .. } => assert_eq!(val, "foo"),
            other => panic!("not in static storage: {:?}", other),
        }
    }

    #[test]
    fn storage_small() {

        let text = TestAny::new("foo").unwrap();
        match text {
            Text { storage: Storage::Small(ref val), .. } => assert_eq!(val.as_str(), "foo"),
            other => panic!("not in small storage: {:?}", other),
        }
    }

    #[test]
    fn storage_dynamic() {

        let long: String = (0..100).map(|_| "X").collect();
        let text = TestAny::new(&long).unwrap();
        match text {
            Text { storage: Storage::Dynamic(ref val), .. } => assert_eq!(&val[..], &long),
            other => panic!("not in dynamic storage: {:?}", other),
        }
    }
}
