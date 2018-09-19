//! Predefined constraints.

use std::error;
use std::fmt;

/// Allow all values with no additional constraints.
///
/// The `Text` type provides some convenience functions to skip
/// validation when this `Check` is used.
///
/// Only use this for really unconstraint kinds of text. It is unsuited
/// for prototyping since a switch to another constraint will make the
/// `Any` specific functions on `Text` unavailable.
#[derive(Debug)]
pub enum Any {}

impl ::Check for Any {

    type Error = NoError;

    fn check(_value: &str) -> Result<(), Self::Error> { Ok(()) }
}

/// Unconstructable error that never happens.
///
/// Used by `check::Any` as error type. The type is a variant-less enum
/// and as such can never be constructed.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum NoError {}

impl fmt::Display for NoError {

    // Not reachable because `NoError` has no variants.
    fn fmt(&self, _fmt: &mut fmt::Formatter) -> fmt::Result { unreachable!() }
}

impl error::Error for NoError {

    // Not reachable because `NoError` has no variants.
    fn description(&self) -> &str { unreachable!() }
}
