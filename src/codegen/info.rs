use super::func::FunctionInfo;
use koopa::ir::{Program, Value};
use std::collections::HashMap;

/// Some necessary information during assembly generation.
pub struct ProgramInfo<'p> {
  program: &'p Program,
  values: HashMap<Value, String>,
  cur_func: Option<FunctionInfo>,
}

/// Returns a reference to the current function information.
macro_rules! cur_func {
  ($info:expr) => {
    $info.cur_func().unwrap()
  };
}
pub(crate) use cur_func;

/// Returns a mutable reference to the current function information.
macro_rules! cur_func_mut {
  ($info:expr) => {
    $info.cur_func_mut().unwrap()
  };
}
pub(crate) use cur_func_mut;

impl<'p> ProgramInfo<'p> {
  /// Creates a new program information.
  pub fn new(program: &'p Program) -> Self {
    Self {
      program,
      values: HashMap::new(),
      cur_func: None,
    }
  }

  /// Returns a reference to the program.
  pub fn program(&self) -> &'p Program {
    self.program
  }

  /// Returns the name of the given global value.
  pub fn value(&self, value: Value) -> &str {
    self.values.get(&value).unwrap()
  }

  /// Inserts a new global value name.
  pub fn insert_value(&mut self, value: Value, name: String) {
    self.values.insert(value, name);
  }

  /// Returns a reference to the current function information.
  pub fn cur_func(&self) -> Option<&FunctionInfo> {
    self.cur_func.as_ref()
  }

  /// Returns a mutable reference to the current function information.
  pub fn cur_func_mut(&mut self) -> Option<&mut FunctionInfo> {
    self.cur_func.as_mut()
  }

  /// Sets the current function information.
  pub fn set_cur_func(&mut self, func: FunctionInfo) {
    self.cur_func = Some(func);
  }
}
