use super::scopes::{cur_func, Scopes};
use super::{Error, Result};
use koopa::ir::builder_traits::*;
use koopa::ir::Value as IrValue;
use koopa::ir::{Program, Type};

/// A value.
pub enum Value {
  /// Koopa IR value.
  Value(IrValue),
  /// Constant integer.
  Const(i32),
}

/// An initializer.
pub enum Initializer {
  Const(i32),
  Value(IrValue),
  List(Vec<Initializer>),
}

impl Initializer {
  /// Reshapes the current initializer by using the given type.
  /// Returns the reshaped initializer.
  pub fn reshape(self, ty: &Type) -> Result<Initializer> {
    todo!()
  }

  /// Converts the initializer (must be reshaped first) into a constant.
  pub fn into_const(self, program: &mut Program, scopes: &Scopes) -> Result<IrValue> {
    match self {
      Self::Const(num) => Ok(if scopes.is_global() {
        program.new_value().integer(num)
      } else {
        cur_func!(scopes).new_value(program).integer(num)
      }),
      Self::Value(_) => Err(Error::FailedToEval),
      Self::List(list) => {
        let values = list
          .into_iter()
          .map(|i| i.into_const(program, scopes))
          .collect::<Result<_>>()?;
        Ok(if scopes.is_global() {
          program.new_value().aggregate(values)
        } else {
          cur_func!(scopes).new_value(program).aggregate(values)
        })
      }
    }
  }

  /// Converts the initializer (must be reshaped first)
  /// into store instructions.
  pub fn into_stores(self, program: &mut Program, scopes: &Scopes, ptr: IrValue) {
    let info = cur_func!(scopes);
    let store = match self {
      Self::Const(num) => {
        let value = info.new_value(program).integer(num);
        info.new_value(program).store(value, ptr)
      }
      Self::Value(value) => info.new_value(program).store(value, ptr),
      Self::List(list) => {
        for (i, init) in list.into_iter().enumerate() {
          let index = info.new_value(program).integer(i as i32);
          let ptr = info.new_value(program).get_elem_ptr(ptr, index);
          init.into_stores(program, scopes, ptr);
        }
        return;
      }
    };
    info.push_inst(program, store);
  }
}

/// An expression value.
pub enum ExpValue {
  /// An `void`.
  Void,
  /// An integer.
  Int(IrValue),
  /// An integer pointer.
  IntPtr(IrValue),
  /// An array pointer (part of array).
  ArrPtr(IrValue),
}

impl ExpValue {
  /// Converts the value into a right value.
  pub fn into_val(self, program: &mut Program, scopes: &Scopes) -> Result<IrValue> {
    match self {
      Self::Void => Err(Error::UseVoidValue),
      Self::Int(val) => Ok(val),
      Self::IntPtr(ptr) => {
        let info = cur_func!(scopes);
        let load = info.new_value(program).load(ptr);
        info.push_inst(program, load);
        Ok(load)
      }
      Self::ArrPtr(ptr) => Ok(ptr),
    }
  }

  /// Converts the value into a integer right value.
  pub fn into_int(self, program: &mut Program, scopes: &Scopes) -> Result<IrValue> {
    match self {
      Self::ArrPtr(_) => Err(Error::NonIntCalc),
      _ => self.into_val(program, scopes),
    }
  }

  /// Converts the value into a left-value pointer.
  pub fn into_ptr(self) -> Result<IrValue> {
    match self {
      Self::IntPtr(ptr) => Ok(ptr),
      Self::ArrPtr(_) => Err(Error::ArrayAssign),
      _ => unreachable!(),
    }
  }
}
