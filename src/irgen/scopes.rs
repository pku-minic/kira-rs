use super::func::FunctionInfo;
use super::values::Value;
use super::{Error, Result};
use koopa::ir::Value as IrValue;
use koopa::ir::{BasicBlock, Function, Program, Type};
use std::collections::HashMap;

/// Scopes, including all values, constants and functions definitions.
pub struct Scopes<'ast> {
  vals: Vec<HashMap<&'ast str, Value>>,
  funcs: HashMap<&'ast str, Function>,
  pub cur_func: Option<FunctionInfo>,
  pub loop_info: Vec<(BasicBlock, BasicBlock)>,
}

/// Returns a reference to the current function information.
macro_rules! cur_func {
  ($scopes:expr) => {
    $scopes.cur_func.as_ref().unwrap()
  };
}
pub(crate) use cur_func;

/// Returns a mutable reference to the current function information.
macro_rules! cur_func_mut {
  ($scopes:expr) => {
    $scopes.cur_func.as_mut().unwrap()
  };
}
pub(crate) use cur_func_mut;

impl<'ast> Scopes<'ast> {
  /// Creates a new `Scopes`.
  pub fn new() -> Self {
    Self {
      vals: vec![HashMap::new()],
      funcs: HashMap::new(),
      cur_func: None,
      loop_info: Vec::new(),
    }
  }

  /// Returns `true` if is currently in global scope.
  pub fn is_global(&self) -> bool {
    self.cur_func.is_none()
  }

  /// Inserts a new value to the current scope.
  pub fn new_value(&mut self, id: &'ast str, value: Value) -> Result<()> {
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
  pub fn value(&self, id: &str) -> Result<&Value> {
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
  pub fn new_func(&mut self, id: &'ast str, func: Function) -> Result<()> {
    if self.funcs.contains_key(id) || self.vals.first().unwrap().contains_key(id) {
      Err(Error::DuplicatedDef)
    } else {
      self.funcs.insert(id, func);
      Ok(())
    }
  }

  /// Returns the function by the given identifier.
  pub fn func(&self, id: &str) -> Result<Function> {
    self.funcs.get(id).copied().ok_or(Error::SymbolNotFound)
  }

  /// Enters a new scope.
  pub fn enter(&mut self) {
    self.vals.push(HashMap::new());
  }

  /// Exits from the current scope.
  pub fn exit(&mut self) {
    self.vals.pop();
  }

  /// Returns type of the given value.
  pub fn ty(&self, program: &Program, value: IrValue) -> Type {
    if value.is_global() {
      program.borrow_value(value).ty().clone()
    } else {
      program
        .func(cur_func!(self).func())
        .dfg()
        .value(value)
        .ty()
        .clone()
    }
  }
}
