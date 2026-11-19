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
    ("+(1 || getint())", 1),
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

fn assert_ir_error(source: &str, expected: Error) {
  let ast = CompUnitParser::new().parse(source).unwrap();
  assert_eq!(generate_program(&ast).err(), Some(expected), "{source}");
}

#[test]
fn constant_expressions_resolve_names_before_evaluation() {
  for source in [
    "const int c = missing;",
    "const int c = 0 && missing;",
    "const int c = 0 && ((1 / 0) + missing);",
    "int f() { const int c = 1 || missing(); return c; }",
    "int a[2]; int g = 1 || a[missing];",
    "int a[1 || missing];",
    "int f(int a[][1 || missing]) { return 0; }",
    "int f(int n) { return n; } const int c = (1 / 0) + f(missing);",
  ] {
    assert_ir_error(source, Error::SymbolNotFound);
  }
}

#[test]
fn constant_expressions_check_operand_types() {
  for (source, expected) in [
    ("const int c = 1 || putint(1);", Error::UseVoidValue),
    ("int a[2]; const int c = 0 && a;", Error::NonIntCalc),
    ("const int n = 1, c = 1 || n[0];", Error::DerefInt),
    ("int a[2]; int c = 0 && a[a];", Error::NonIntCalc),
    ("int c = 1 || getint(0);", Error::ArgMismatch),
    ("int c = 1 || getarray(0);", Error::ArgMismatch),
    ("int a[2][3]; int c = 1 || getarray(a);", Error::ArgMismatch),
    ("int a[2]; int c = 1 || getarray(+a);", Error::NonIntCalc),
  ] {
    assert_ir_error(source, expected);
  }
}

#[test]
fn runtime_values_are_only_needed_on_evaluated_paths() {
  let source = "int a[2][3]; const int c = 1 || getarray(a[1 / 0]); \
                int f(int p[][3]) { const int d = 0 && (p[0][0] + getarray(p[1])); return d; }";
  let ast = CompUnitParser::new().parse(source).unwrap();
  assert!(generate_program(&ast).is_ok());
  assert_ir_error("int c = 0 || getint();", Error::FailedToEval);
  assert_ir_error("int n; const int c = 1 && n;", Error::FailedToEval);
}

#[test]
fn parameters_can_shadow_function_names() {
  for source in [
    "int f(int putint) { return putint; } int main() { return f(42); }",
    "int g() { return 1; } int f(int g) { return g; } int main() { return f(42); }",
    "int f(int f) { return f; } int main() { return f(42); }",
  ] {
    let ast = CompUnitParser::new().parse(source).unwrap();
    assert!(generate_program(&ast).is_ok(), "{source}");
  }
}

#[test]
fn duplicate_parameters_and_global_names_are_rejected() {
  for source in [
    "int f(int value, int value) { return value; }",
    "int putint;",
    "int f() { return 1; } int f;",
    "int f; int f() { return 1; }",
  ] {
    let ast = CompUnitParser::new().parse(source).unwrap();
    assert!(
      matches!(generate_program(&ast), Err(Error::DuplicatedDef)),
      "{source}"
    );
  }
}
