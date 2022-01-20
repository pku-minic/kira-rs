use crate::ast::*;
use koopa::ir::{Function, Program};
use std::collections::HashMap;
use std::fmt;

/// Generates Koopa IR program for the given compile unit (ASTs).
pub fn generate_program(comp_unit: &CompUnit) -> Result<Program> {
  let mut program = Program::new();
  comp_unit.generate(&mut program, &mut Scopes::new())?;
  Ok(program)
}

/// Scopes, including all values, constants and functions definitions.
struct Scopes<'ast> {
  vals: Vec<HashMap<&'ast str, Value>>,
  funcs: HashMap<&'ast str, Function>,
}

impl<'ast> Scopes<'ast> {
  /// Creates a new `Scopes`.
  fn new() -> Self {
    Self {
      vals: vec![HashMap::new()],
      funcs: HashMap::new(),
    }
  }

  /// Returns `true` if is currently in global scope.
  fn is_global(&self) -> bool {
    self.vals.len() == 1
  }

  /// Inserts a new value to the current scope.
  fn new_value(&mut self, id: &'ast str, value: Value) -> Result<()> {
    let is_global = self.is_global();
    let cur = self.vals.last_mut().unwrap();
    if cur.contains_key(id) || (is_global && self.funcs.contains_key(id)) {
      Err(Error::DuplicatedDef)
    } else {
      cur.insert(id, value);
      Ok(())
    }
  }

  /// Returns the value by the given identifier.
  fn value(&self, id: &str) -> Result<&Value> {
    let mut cur = self.vals.len() as i32 - 1;
    while cur >= 0 {
      if let Some(value) = self.vals[cur as usize].get(id) {
        return Ok(value);
      }
      cur -= 1;
    }
    Err(Error::SymbolNotFound)
  }

  /// Inserts a new function to the current scope.
  fn new_func(&mut self, id: &'ast str, func: Function) -> Result<()> {
    if self.funcs.contains_key(id) || self.vals.first().unwrap().contains_key(id) {
      Err(Error::DuplicatedDef)
    } else {
      self.funcs.insert(id, func);
      Ok(())
    }
  }

  /// Returns the function by the given identifier.
  fn func(&self, id: &str) -> Result<Function> {
    self.funcs.get(id).copied().ok_or(Error::SymbolNotFound)
  }
}

/// A value.
enum Value {
  /// Koopa IR value.
  Value(koopa::ir::Value),
  /// Constant integer.
  Int(i32),
  /// Constant zeros (zeroed array).
  Zeros,
  /// Constant array.
  Array(Vec<i32>),
}

/// Error returned by IR generator.
pub enum Error {
  DuplicatedDef,
  SymbolNotFound,
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::DuplicatedDef => write!(f, "duplicated symbol definition"),
      Self::SymbolNotFound => write!(f, "symbol not found"),
    }
  }
}

/// Result type of IR generator.
pub type Result<T> = std::result::Result<T, Error>;

trait GenerateProgram<'ast> {
  type Out;

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out>;
}

impl<'ast> GenerateProgram<'ast> for CompUnit {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    for item in &self.items {
      item.generate(program, scopes)?;
    }
    Ok(())
  }
}

impl<'ast> GenerateProgram<'ast> for GlobalItem {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    match self {
      Self::Decl(decl) => decl.generate(program, scopes),
      Self::FuncDef(def) => def.generate(program, scopes),
    }
  }
}

impl<'ast> GenerateProgram<'ast> for Decl {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    match self {
      Self::Const(c) => c.generate(program, scopes),
      Self::Var(v) => v.generate(program, scopes),
    }
  }
}

impl<'ast> GenerateProgram<'ast> for ConstDecl {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    for def in &self.defs {
      def.generate(program, scopes)?;
    }
    Ok(())
  }
}

impl<'ast> GenerateProgram<'ast> for ConstDef {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for ConstInitVal {
  type Out = Value;

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for VarDecl {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for VarDef {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for InitVal {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for FuncDef {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for FuncType {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for FuncFParam {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for Block {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for BlockItem {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for Stmt {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for Assign {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for ExpStmt {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for If {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for While {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for Return {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for Exp {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for LVal {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for PrimaryExp {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for UnaryExp {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for FuncCall {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for MulExp {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for AddExp {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for RelExp {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for EqExp {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for LAndExp {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for LOrExp {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for ConstExp {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for UnaryOp {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for MulOp {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for AddOp {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for RelOp {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for EqOp {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}
