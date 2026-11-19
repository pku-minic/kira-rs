use super::scopes::Scopes;
use super::values::Value;
use super::{Error, Result};
use crate::ast::*;
use koopa::ir::{Function, Program, Type, TypeKind};

/// Checks an expression used as a value without evaluating it or emitting IR.
pub(super) trait CheckType {
  fn value_type(&self, program: &Program, scopes: &Scopes) -> Result<Type>;

  fn check_int(&self, program: &Program, scopes: &Scopes) -> Result<()> {
    if self.value_type(program, scopes)?.is_i32() {
      Ok(())
    } else {
      Err(Error::NonIntCalc)
    }
  }
}

impl CheckType for Exp {
  fn value_type(&self, program: &Program, scopes: &Scopes) -> Result<Type> {
    self.lor.value_type(program, scopes)
  }
}

impl CheckType for LVal {
  fn value_type(&self, program: &Program, scopes: &Scopes) -> Result<Type> {
    let mut ty = match scopes.value(&self.id)? {
      Value::Const(_) => Type::get_i32(),
      Value::Value(alloc) => {
        let storage = scopes.ty(program, *alloc);
        let TypeKind::Pointer(base) = storage.kind() else {
          unreachable!("variable bindings refer to allocations")
        };
        base.clone()
      }
    };
    for index in &self.indices {
      ty = match ty.kind() {
        TypeKind::Array(base, _) | TypeKind::Pointer(base) => base.clone(),
        _ => return Err(Error::DerefInt),
      };
      index.check_int(program, scopes)?;
    }
    // An array used as a value decays to a pointer to its first element.
    Ok(match ty.kind() {
      TypeKind::Array(base, _) => Type::get_pointer(base.clone()),
      _ => ty,
    })
  }
}

impl CheckType for UnaryExp {
  fn value_type(&self, program: &Program, scopes: &Scopes) -> Result<Type> {
    match self {
      Self::Primary(PrimaryExp::Exp(exp)) => exp.value_type(program, scopes),
      Self::Primary(PrimaryExp::LVal(lval)) => lval.value_type(program, scopes),
      Self::Primary(PrimaryExp::Number(_)) => Ok(Type::get_i32()),
      Self::Unary(_, exp) => {
        exp.check_int(program, scopes)?;
        Ok(Type::get_i32())
      }
      Self::Call(call) => {
        let func = scopes.func(&call.id)?;
        let args = call
          .args
          .iter()
          .map(|arg| arg.value_type(program, scopes))
          .collect::<Result<Vec<_>>>()?;
        let ret = call_result_type(program, func, args.into_iter())?;
        if ret.is_unit() {
          Err(Error::UseVoidValue)
        } else {
          Ok(ret)
        }
      }
    }
  }
}

/// Checks argument count and types for both constant expressions and emitted calls.
pub(super) fn call_result_type(
  program: &Program,
  func: Function,
  args: impl Iterator<Item = Type>,
) -> Result<Type> {
  let TypeKind::Function(params, ret) = program.func(func).ty().kind() else {
    unreachable!()
  };
  if params.iter().cloned().eq(args) {
    Ok(ret.clone())
  } else {
    Err(Error::ArgMismatch)
  }
}

// Every binary operator in the SysY expression grammar takes and returns integers.
macro_rules! check_binary {
  ($ty:ident, $inner:ident, $binary:ident) => {
    impl CheckType for $ty {
      fn value_type(&self, program: &Program, scopes: &Scopes) -> Result<Type> {
        match self {
          Self::$inner(exp) => exp.value_type(program, scopes),
          Self::$binary(lhs, .., rhs) => {
            lhs.check_int(program, scopes)?;
            rhs.check_int(program, scopes)?;
            Ok(Type::get_i32())
          }
        }
      }
    }
  };
}

check_binary!(MulExp, Unary, MulUnary);
check_binary!(AddExp, Mul, AddMul);
check_binary!(RelExp, Add, RelAdd);
check_binary!(EqExp, Rel, EqRel);
check_binary!(LAndExp, Eq, LAndEq);
check_binary!(LOrExp, LAnd, LOrLAnd);
