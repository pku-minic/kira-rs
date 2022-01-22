mod eval;
mod func;
mod gen;
mod scopes;
mod values;

use crate::ast::{CompUnit, ConstExp};
use eval::Evaluate;
use gen::GenerateProgram;
use koopa::ir::{Program, Type};
use scopes::Scopes;
use std::fmt;

/// Generates Koopa IR program for the given compile unit (ASTs).
pub fn generate_program(comp_unit: &CompUnit) -> Result<Program> {
  let mut program = Program::new();
  comp_unit.generate(&mut program, &mut Scopes::new())?;
  Ok(program)
}

/// Error returned by IR generator.
pub enum Error {
  DuplicatedDef,
  SymbolNotFound,
  FailedToEval,
  InvalidArrayLen,
  ArrayAssign,
  NotInLoop,
  RetValInVoidFunc,
  DerefInt,
  UseVoidValue,
  ArgMismatch,
  NonIntCalc,
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::DuplicatedDef => write!(f, "duplicated symbol definition"),
      Self::SymbolNotFound => write!(f, "symbol not found"),
      Self::FailedToEval => write!(f, "failed to evaluate constant"),
      Self::InvalidArrayLen => write!(f, "invalid array length"),
      Self::ArrayAssign => write!(f, "assigning to array"),
      Self::NotInLoop => write!(f, "using break/continue outside of loop"),
      Self::RetValInVoidFunc => write!(f, "returning value in void fucntion"),
      Self::DerefInt => write!(f, "dereferencing an integer"),
      Self::UseVoidValue => write!(f, "using a void value"),
      Self::ArgMismatch => write!(f, "argument mismatch"),
      Self::NonIntCalc => write!(f, "non-integer calculation"),
    }
  }
}

impl fmt::Debug for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self)
  }
}

/// Result type of IR generator.
pub type Result<T> = std::result::Result<T, Error>;

/// Helper trait for converting dimentions to type.
pub(crate) trait DimsToType {
  fn to_type(&self, scopes: &Scopes) -> Result<Type>;
}

impl DimsToType for Vec<ConstExp> {
  fn to_type(&self, scopes: &Scopes) -> Result<Type> {
    self.iter().rev().fold(Ok(Type::get_i32()), |b, exp| {
      let base = b?;
      let len = exp.eval(scopes).ok_or(Error::FailedToEval)?;
      (len >= 1)
        .then(|| Type::get_array(base, len as usize))
        .ok_or(Error::InvalidArrayLen)
    })
  }
}
