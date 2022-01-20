use crate::ast::*;
use koopa::ir::{Function, Program, Value};
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
  consts: Vec<HashMap<&'ast str, i32>>,
  funcs: HashMap<&'ast str, Function>,
}

impl<'ast> Scopes<'ast> {
  fn new() -> Self {
    Self {
      vals: vec![HashMap::new()],
      consts: vec![HashMap::new()],
      funcs: HashMap::new(),
    }
  }
}

/// Error returned by IR generator.
pub struct Error();

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    todo!()
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
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for ConstDef {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for ConstInitVal {
  type Out = ();

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
