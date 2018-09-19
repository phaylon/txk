
/// Type constraints.
///
/// Any type implementing this trait can be used as a type constraint
/// for `Text` types via `Kind::Check`.
///
/// # Examples
///
/// ```
/// // An error to return if the validation fails.
/// #[derive(Debug, PartialEq, Eq)]
/// struct NotEmptyError;
///
/// // The constraint type.
/// struct NotEmptyCheck;
///
/// // Turning the type into a constraint.
/// impl txk::Check for NotEmptyCheck {
///
///     // Declare our error type as the validation error type.
///     type Error = NotEmptyError;
///
///     // Our validation routine.
///     // It will return our error when the value is empty.
///     fn check(value: &str) -> Result<(), Self::Error> {
///         if !value.is_empty() { Ok(()) }
///         else { Err(NotEmptyError) }
///     }
/// }
///
/// // A `Kind` using our new `Check` constraint.
/// struct MyKind;
/// impl txk::Kind for MyKind {
///     type Check = NotEmptyCheck;
///     const NAME: &'static str = "test kind";
/// }
///
/// // A value passing our constraint.
/// let result: Result<txk::Text<MyKind>, _> =
///     txk::Text::new("foo");
/// assert!(result.is_ok());
/// let value = result.expect("valid value");
/// assert_eq!(value, "foo");
///
/// // A value failing our constraint.
/// let result: Result<txk::Text<MyKind>, _> =
///     txk::Text::new("");
/// assert!(result.is_err());
/// let error = result.err().expect("error");
/// assert_eq!(error.inner(), &NotEmptyError);
///
/// ```
pub trait Check: 'static {

    /// The type representing a validation error.
    type Error;

    /// This function performs the validation.
    ///
    /// It returns `Ok(())` when the value is valid and `Err(_)` containing
    /// the `Self::Error` on failure.
    fn check(value: &str) -> Result<(), Self::Error>;
}

/// Distinct text kinds.
///
/// This trait is implemented by types identifying the distinct types of
/// text.
///
/// # Examples
///
/// ```
/// // A kind type.
/// struct Title;
///
/// // Turn the type into an actual `Kind`.
/// impl txk::Kind for Title {
///
///     // Associate a value constraint with the kind.
///     type Check = txk::check::Any;
///
///     // Give the kind a name for use in errors.
///     const NAME: &'static str = "title";
/// }
///
/// // Construct a value of the declared kind.
/// // We're allowed to use `new_any` since the `Check` is `check::Any`.
/// let value: txk::Text<Title> = txk::Text::new_any("foo");
///
/// assert_eq!(value, "foo");
/// ```
pub trait Kind: 'static {

    /// The value constraint type.
    type Check: Check;

    /// A name for the kind of text to be used in error messages.
    ///
    /// This should be a simple lowercase noun, for use in messages such
    /// as `"invalid <NAME>"`.
    const NAME: &'static str;
}

