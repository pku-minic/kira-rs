use super::{Error, generate_program};
use crate::sysy::CompUnitParser;
use koopa::ir::ValueKind;

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

#[test]
fn logical_constants_short_circuit() {
  for (expression, expected) in [
    ("0 && (1 / 0)", 0),
    ("1 || (1 / 0)", 1),
    ("0 && (1 % 0)", 0),
    ("-3 || (1 % 0)", 1),
    ("2 && 4", 1),
    ("0 || -7", 1),
    ("1 && 0", 0),
    ("0 || 0", 0),
    ("1 && (0 || (8 / 2))", 1),
    ("(0 && (1 / 0)) || (2 && 3)", 1),
  ] {
    let source = format!(
      "const int value = {expression}; int actual = value; \
       int main() {{ const int local = {expression}; return local; }}"
    );
    let ast = CompUnitParser::new().parse(&source).unwrap();
    let program = generate_program(&ast).unwrap();
    let global = program.borrow_value(program.inst_layout()[0]);
    let ValueKind::GlobalAlloc(alloc) = global.kind() else {
      panic!("expected the actual global allocation");
    };
    let initializer = program.borrow_value(alloc.init());
    let ValueKind::Integer(value) = initializer.kind() else {
      panic!("expected an integer initializer");
    };
    assert_eq!(value.value(), expected, "{expression}");
  }
}

#[test]
fn logical_constants_evaluate_required_operands() {
  for expression in ["1 && (1 / 0)", "0 || (1 / 0)"] {
    let source = format!("const int value = {expression};");
    let ast = CompUnitParser::new().parse(&source).unwrap();
    assert!(matches!(generate_program(&ast), Err(Error::FailedToEval)));
  }
}
