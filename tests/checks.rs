
extern crate txk;

#[test]
fn any() {

    struct TestKind;

    impl txk::Kind for TestKind {

        type Check = txk::check::Any;

        const NAME: &'static str = "Any";
    }

    type Test = txk::Text<TestKind>;

    let _ = Test::new("").unwrap();
    let _ = Test::new("foo bar").unwrap();
}
