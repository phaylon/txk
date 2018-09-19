
use std::cmp;
use std::error;
use std::fmt;
use std::hash;

/// A general validation error.
///
/// The error returned by the `Check` constraint of the `Kind` is stored
/// inside this error.
///
/// The purpose of this type is to add a leading error in the causal error
/// chain reporting `"invalid <NAME>"` using the `Kind::NAME` value as
/// name for the kind.
///
/// Note that the failed values are not attached to the errors. This is
/// because the requirements in terms of value storage and display logic
/// are too broad. This fact also makes it easier not to accidentally leak
/// failed values in error data.
pub struct Error<K>
where
    K: ::Kind,
{
    inner: <K::Check as ::Check>::Error,
}

impl<K> Error<K>
where
    K: ::Kind,
{
    /// Constructs a new error.
    ///
    /// The type of the `inner` value must be the same as `K`s `Check::Error`.
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
    /// let error: txk::Error<MyKind> =
    ///     txk::Error::new(NotEmptyError);
    /// ```
    pub fn new(inner: <K::Check as ::Check>::Error) -> Error<K> {
        Error { inner }
    }

    /// Get a reference to the inner `Check` error.
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
    /// let error: txk::Error<MyKind> =
    ///     txk::Error::new(NotEmptyError);
    /// let inner: &NotEmptyError = error.inner();
    /// ```
    pub fn inner(&self) -> &<K::Check as ::Check>::Error {
        &self.inner
    }

    /// Unwrap the outer error into the inner `Check` error.
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
    /// let error: txk::Error<MyKind> =
    ///     txk::Error::new(NotEmptyError);
    /// let inner: NotEmptyError = error.into_inner();
    /// ```
    pub fn into_inner(self) -> <K::Check as ::Check>::Error {
        self.inner
    }
}

impl<K> fmt::Debug for Error<K>
where
    K: ::Kind,
    <K::Check as ::Check>::Error: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("Error").field("inner", &self.inner).finish()
    }
}

impl<K> fmt::Display for Error<K>
where
    K: ::Kind,
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "invalid {}", K::NAME)
    }
}

impl<K> Clone for Error<K>
where
    K: ::Kind,
    <K::Check as ::Check>::Error: Clone,
{
    fn clone(&self) -> Error<K> {
        Error {
            inner: self.inner.clone(),
        }
    }
}

impl<K> error::Error for Error<K>
where
    K: ::Kind,
    <K::Check as ::Check>::Error: error::Error,
{
    fn description(&self) -> &str { "txk validation error" }

    fn cause(&self) -> Option<&error::Error> {
        Some(&self.inner)
    }
}

impl<K> cmp::PartialEq for Error<K>
where
    K: ::Kind,
    <K::Check as ::Check>::Error: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.inner.eq(&other.inner)
    }
}

impl<K> cmp::Eq for Error<K>
where
    K: ::Kind,
    <K::Check as ::Check>::Error: Eq,
{}

impl<K> cmp::PartialOrd for Error<K>
where
    K: ::Kind,
    <K::Check as ::Check>::Error: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.inner.partial_cmp(&other.inner)
    }
}

impl<K> cmp::Ord for Error<K>
where
    K: ::Kind,
    <K::Check as ::Check>::Error: Ord,
{
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.inner.cmp(&other.inner)
    }
}

impl<K> hash::Hash for Error<K>
where
    K: ::Kind,
    <K::Check as ::Check>::Error: hash::Hash,
{
    fn hash<H>(&self, state: &mut H)
    where
        H: hash::Hasher,
    {
        self.inner.hash(state);
    }
}

