
extern crate txk;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TestError(i32);

impl ::std::fmt::Display for TestError {

    fn fmt(&self, fmt: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        ::std::fmt::Display::fmt(&self.0, fmt)
    }
}

impl ::std::error::Error for TestError {

    fn description(&self) -> &str { "test error" }
}

struct TestCheck;

impl txk::Check for TestCheck {

    type Error = TestError;

    fn check(_: &str) -> Result<(), Self::Error> {
        unimplemented!();
    }
}

struct TestKind;

impl txk::Kind for TestKind {

    type Check = TestCheck;

    const NAME: &'static str = "test kind";
}

fn make_error(value: i32) -> txk::Error<TestKind> {
    txk::Error::new(TestError(value))
}

#[test]
fn error() {
    use std::error::{Error};

    let error = make_error(23);
    assert_eq!(error.description(), "txk validation error");

    let error = error.cause().expect("inner error");
    assert_eq!(error.description(), "test error");
    assert_eq!(&format!("{}", error), "23");
}

#[test]
fn debug() {
    
    let error = make_error(23);

    let result = format!("{:?}", error);
    assert!(result.starts_with("Error {"));
    assert!(result.ends_with("}"));
    assert!(result.contains("inner"));
    assert!(result.contains("TestError"));
    assert!(result.contains("23"));
}

#[test]
fn display() {
    
    let error = make_error(23);

    let result = format!("{}", error);
    assert_eq!(&result, "invalid test kind");
}

#[test]
fn clone() {

    let error_1 = make_error(23);
    let error_2 = error_1.clone();

    assert_eq!(error_1, error_2);
}

#[test]
fn partial_eq() {
    use std::cmp;

    let error = make_error(23);
    let error_same = make_error(23);
    let error_diff = make_error(42);

    assert!(cmp::PartialEq::eq(&error, &error_same));
    assert!(!cmp::PartialEq::eq(&error, &error_diff));
}

#[test]
fn eq_operator() {

    let error = make_error(23);
    let error_same = make_error(23);
    let error_diff = make_error(42);

    assert!(error == error_same);
    assert!(error != error_diff);
}

#[test]
fn partial_ord() {
    use std::cmp;

    let error_23 = make_error(23);
    let error_42 = make_error(42);

    assert_eq!(cmp::PartialOrd::partial_cmp(&error_23, &error_42), Some(cmp::Ordering::Less));
    assert_eq!(cmp::PartialOrd::partial_cmp(&error_42, &error_23), Some(cmp::Ordering::Greater));
    assert_eq!(cmp::PartialOrd::partial_cmp(&error_23, &error_23), Some(cmp::Ordering::Equal));
}

#[test]
fn ord() {
    use std::cmp;

    let error_23 = make_error(23);
    let error_42 = make_error(42);

    assert_eq!(cmp::Ord::cmp(&error_23, &error_42), cmp::Ordering::Less);
    assert_eq!(cmp::Ord::cmp(&error_42, &error_23), cmp::Ordering::Greater);
    assert_eq!(cmp::Ord::cmp(&error_23, &error_23), cmp::Ordering::Equal);
}

#[test]
fn ord_operators() {

    let error_23 = make_error(23);
    let error_42 = make_error(42);

    assert!(error_23 < error_42);
    assert!(error_23 <= error_42);
    assert!(error_23 <= error_23);

    assert!(error_42 > error_23);
    assert!(error_42 >= error_23);
    assert!(error_23 >= error_23);
}

#[test]
fn hash() {
    use std::collections;

    let error = make_error(23);
    let error_diff = make_error(42);

    let mut hmap = collections::HashMap::new();
    hmap.insert(error.clone(), 23);
    assert_eq!(hmap.get(&error), Some(&23));
    assert_eq!(hmap.get(&error_diff), None);
}

