#![cfg(feature = "serde")]

extern crate txk;
extern crate serde;
extern crate serde_json;

#[derive(Debug)]
pub struct TestError;

pub struct TestCheck;

impl txk::Check for TestCheck {
    type Error = TestError;
    fn check(value: &str) -> Result<(), Self::Error> {
        if value.is_empty() { Err(TestError) }
        else { Ok(()) }
    }
}

pub struct TestKind;

impl txk::Kind for TestKind {
    type Check = TestCheck;
    const NAME: &'static str = "test kind";
}

#[test]
fn deserialize() {

    let text: txk::Text<TestKind> = serde_json::from_str("\"foo\"").unwrap();
    assert_eq!(text.as_str(), "foo");
}

#[test]
fn deserialize_errors() {

    let result: Result<txk::Text<TestKind>, _> = serde_json::from_str("\"\"");
    let error = result.err().expect("empty string should fail");
    assert!(format!("{}", error).contains("invalid test kind"));
}

#[test]
fn serialize() {

    let text: txk::Text<TestKind> = serde_json::from_str("\"foo\"").unwrap();
    let content = serde_json::to_string(&text).unwrap();
    assert_eq!(&content, "\"foo\"");
}

