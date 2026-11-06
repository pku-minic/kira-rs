use super::{Error, generate_program};
use crate::sysy::CompUnitParser;

#[test]
fn invalid_constant_division_returns_an_error() {
  for expression in [
    "1 / 0",
    "1 % 0",
    "(-2147483647 - 1) / -1",
    "(-2147483647 - 1) % -1",
  ] {
    for source in [
      format!("const int value = {expression}; int main() {{ return value; }}"),
      format!("int main() {{ const int value = {expression}; return value; }}"),
    ] {
      let ast = CompUnitParser::new().parse(&source).unwrap();
      assert!(
        matches!(generate_program(&ast), Err(Error::FailedToEval)),
        "expected a constant-evaluation error for {source}"
      );
    }
  }
}
