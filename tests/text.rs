
extern crate txk;

macro_rules! gen_matching {
    ($alias:ident, $kind:ident, $check:ident, $value:expr) => {
        struct $check;

        impl txk::Check for $check {

            type Error = ();

            fn check(value: &str) -> Result<(), Self::Error> {
                if value == $value { Ok(()) }
                else { Err(()) }
            }
        }

        struct $kind;

        impl txk::Kind for $kind {

            type Check = $check;

            const NAME: &'static str = stringify!($alias);
        }

        type $alias = txk::Text<$kind>;
    }
}

gen_matching!(TestOk, TestOkKind, TestOkCheck, "ok");

gen_matching!(TestDiffOk, TestDiffOkKind, TestDiffOkCheck, "ok");

struct TestOkKind2;

impl txk::Kind for TestOkKind2 {

    type Check = TestOkCheck;

    const NAME: &'static str = "TestOk2";
}

type TestOk2 = txk::Text<TestOkKind2>;

struct TestAnyKind;

impl txk::Kind for TestAnyKind {

    type Check = txk::check::Any;

    const NAME: &'static str = "TestAny";
}

type TestAny = txk::Text<TestAnyKind>;

#[test]
fn new_dynamic() {

    assert!(TestOk::new(String::from("ok")).is_ok());
    assert!(TestOk::new(String::from("foo")).is_err());
}

#[test]
fn new_static() {

    assert!(TestOk::new_from_static("ok").is_ok());
    assert!(TestOk::new_from_static("foo").is_err());
}

#[test]
fn to_other() {

    let ok = TestOk::new("ok").unwrap();
    let ok2: TestOk2 = ok.to_other();
    assert_eq!(ok2.as_str(), "ok");
    assert_eq!(ok, ok2);
}

#[test]
fn into_other() {

    let ok = TestOk::new("ok").unwrap();
    let ok2: TestOk2 = ok.into_other();
    assert_eq!(ok2.as_str(), "ok");
}

#[test]
fn try_to_other() {

    let ok = TestOk::new("ok").unwrap();
    let ok2: TestDiffOk = ok.try_to_other().unwrap();
    assert_eq!(ok2.as_str(), "ok");
    assert_eq!(ok, ok2);
}

#[test]
fn as_other() {

    let ok = TestOk::new("ok").unwrap();
    let ok2: &TestOk2 = ok.as_other();
    assert_eq!(ok2.as_str(), "ok");
    assert_eq!(&ok, ok2);
}

#[test]
fn try_as_other() {

    let ok = TestOk::new("ok").unwrap();
    let ok2: &TestDiffOk = ok.try_as_other().unwrap();
    assert_eq!(ok2.as_str(), "ok");
    assert_eq!(&ok, ok2);
}

#[test]
fn to_any() {

    let ok = TestOk::new("ok").unwrap();
    let ok_any: TestAny = ok.to_any();
    assert_eq!(ok_any.as_str(), "ok");
    assert_eq!(ok, ok_any);
}

#[test]
fn as_any() {

    let ok = TestOk::new("ok").unwrap();
    let ok_any: &TestAny = ok.as_any();
    assert_eq!(ok_any.as_str(), "ok");
    assert_eq!(&ok, ok_any);
}

#[test]
fn into_any() {

    let ok = TestOk::new("ok").unwrap();
    let ok_any: TestAny = ok.into_any();
    assert_eq!(ok_any.as_str(), "ok");
}

#[test]
fn as_str() {

    let ok = TestOk::new("ok").unwrap();
    assert_eq!(ok.as_str(), "ok");
}

#[test]
fn as_bytes() {
    
    let ok = TestOk::new("ok").unwrap();
    assert_eq!(ok.as_bytes(), "ok".as_bytes());
}

#[test]
fn as_static_str() {
    
    let ok = TestOk::new("ok").unwrap();
    assert_eq!(ok.as_static_str(), None);
    
    let ok = TestOk::new_from_static("ok").unwrap();
    assert_eq!(ok.as_static_str(), Some("ok"));

    let other: TestDiffOk = ok.try_to_other().unwrap();
    assert_eq!(other.as_static_str(), Some("ok"));

    let other: TestOk2 = ok.to_other();
    assert_eq!(other.as_static_str(), Some("ok"));

    let other: TestOk2 = ok.into_other();
    assert_eq!(other.as_static_str(), Some("ok"));
}

#[test]
fn deref() {
    
    let ok = TestOk::new("ok").unwrap();
    let s: &str = &*ok;
    assert_eq!(s, "ok");
}

#[test]
fn from_str() {

    let ok: TestOk = "ok".parse().unwrap();
    assert_eq!(ok.as_str(), "ok");
}

#[test]
fn as_ref() {

    let ok = TestOk::new("ok").unwrap();
    assert_eq!(AsRef::<str>::as_ref(&ok), "ok");
    assert_eq!(AsRef::<[u8]>::as_ref(&ok), "ok".as_bytes());
}

#[test]
fn hash() {
    use std::collections;

    let ok = TestAny::new("ok").unwrap();
    let diff = TestAny::new("diff").unwrap();
    let mut hmap = collections::HashMap::new();
    hmap.insert(ok.clone(), 23);
    assert_eq!(hmap.get(&ok), Some(&23));
    assert_eq!(hmap.get(&diff), None);
}

#[test]
fn partial_eq() {
    use std::cmp;

    let ok = TestOk::new("ok").unwrap();
    assert!(cmp::PartialEq::eq(&ok, &"ok"));
    assert!(!cmp::PartialEq::eq(&ok, &"not ok"));
    assert!(cmp::PartialEq::eq(&ok, &TestDiffOk::new("ok").unwrap()));
    assert!(cmp::PartialEq::eq(&ok, &String::from("ok")));
}

#[test]
fn eq_operator() {

    let ok = TestOk::new("ok").unwrap();
    assert!(ok == "ok");
    assert!(ok != "not ok");
    assert!(ok == TestDiffOk::new("ok").unwrap());
    assert!(ok == String::from("ok"));
}

#[test]
fn partial_ord() {
    use std::cmp;

    let ok = TestOk::new("ok").unwrap();
    assert_eq!(cmp::PartialOrd::partial_cmp(&ok, &"zz"), Some(cmp::Ordering::Less));
    assert_eq!(cmp::PartialOrd::partial_cmp(&ok, &"aa"), Some(cmp::Ordering::Greater));
    assert_eq!(cmp::PartialOrd::partial_cmp(&ok, &"ok"), Some(cmp::Ordering::Equal));
}

#[test]
fn ord() {
    use std::cmp;

    let aa = TestAny::new("aa").unwrap();
    let zz = TestAny::new("zz").unwrap();

    assert_eq!(cmp::Ord::cmp(&aa, &zz), cmp::Ordering::Less);
    assert_eq!(cmp::Ord::cmp(&zz, &aa), cmp::Ordering::Greater);
    assert_eq!(cmp::Ord::cmp(&aa, &aa), cmp::Ordering::Equal);
}

#[test]
fn ord_operators() {

    let ok = TestOk::new("ok").unwrap();
    assert!(ok < "zz");
    assert!(ok <= "zz");
    assert!(ok <= "ok");
    assert!(ok > "aa");
    assert!(ok >= "aa");
    assert!(ok >= "ok");
}

#[test]
fn to_string() {

    let ok = TestOk::new("ok").unwrap();
    let ok_s: String = ok.to_string();
    assert_eq!(&ok_s, "ok");
}

#[test]
fn borrow() {
    use std::collections;

    let ok = TestOk::new("ok").unwrap();
    let mut hmap = collections::HashMap::new();
    hmap.insert(ok.clone(), 23);
    assert_eq!(hmap.get("ok"), Some(&23));
}

#[test]
fn clone() {
    
    let ok = TestOk::new("ok").unwrap();
    let ok2: TestOk = ok.clone();
    assert_eq!(ok, ok2);
}

#[test]
fn debug() {
    
    let ok = TestOk::new_from_static("ok").unwrap();
    let result = format!("{:?}", ok);
    assert!(result.starts_with("Text {"));
    assert!(result.ends_with("}"));
    assert!(result.contains("Static"));
    assert!(result.contains("\"ok\""));
}

#[test]
fn display() {
    
    let ok = TestOk::new_from_static("ok").unwrap();
    let result = format!("{}", ok);
    assert_eq!(&result, "ok");
}
