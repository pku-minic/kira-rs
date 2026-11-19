use super::check::CheckType;
use super::scopes::Scopes;
use super::values::Value;
use super::{Error, Result};
use crate::ast::*;
use koopa::ir::Program;

impl Exp {
  /// Checks all operands, then evaluates the constant with short-circuit semantics.
  pub(super) fn eval_const(&self, program: &Program, scopes: &Scopes) -> Result<i32> {
    self.check_int(program, scopes)?;
    self.lor.eval(scopes)
  }
}

/// Evaluates a type-checked expression.
trait Evaluate {
  fn eval(&self, scopes: &Scopes) -> Result<i32>;
}

impl Evaluate for LVal {
  fn eval(&self, scopes: &Scopes) -> Result<i32> {
    match scopes.value(&self.id)? {
      Value::Const(i) => Ok(*i),
      Value::Value(_) => Err(Error::FailedToEval),
    }
  }
}

impl Evaluate for PrimaryExp {
  fn eval(&self, scopes: &Scopes) -> Result<i32> {
    match self {
      Self::Exp(exp) => exp.lor.eval(scopes),
      Self::LVal(lval) => lval.eval(scopes),
      Self::Number(num) => Ok(*num),
    }
  }
}

impl Evaluate for UnaryExp {
  fn eval(&self, scopes: &Scopes) -> Result<i32> {
    match self {
      Self::Primary(primary) => primary.eval(scopes),
      Self::Call(_) => Err(Error::FailedToEval),
      Self::Unary(op, exp) => {
        let value = exp.eval(scopes)?;
        Ok(match op {
          UnaryOp::Pos => value,
          UnaryOp::Neg => -value,
          UnaryOp::LNot => (value == 0) as i32,
        })
      }
    }
  }
}

impl Evaluate for MulExp {
  fn eval(&self, scopes: &Scopes) -> Result<i32> {
    match self {
      Self::Unary(exp) => exp.eval(scopes),
      Self::MulUnary(lhs, op, rhs) => {
        let lhs = lhs.eval(scopes)?;
        let rhs = rhs.eval(scopes)?;
        match op {
          MulOp::Mul => Ok(lhs * rhs),
          MulOp::Div => lhs.checked_div(rhs).ok_or(Error::FailedToEval),
          MulOp::Mod => lhs.checked_rem(rhs).ok_or(Error::FailedToEval),
        }
      }
    }
  }
}

impl Evaluate for AddExp {
  fn eval(&self, scopes: &Scopes) -> Result<i32> {
    match self {
      Self::Mul(exp) => exp.eval(scopes),
      Self::AddMul(lhs, op, rhs) => {
        let lhs = lhs.eval(scopes)?;
        let rhs = rhs.eval(scopes)?;
        Ok(match op {
          AddOp::Add => lhs + rhs,
          AddOp::Sub => lhs - rhs,
        })
      }
    }
  }
}

impl Evaluate for RelExp {
  fn eval(&self, scopes: &Scopes) -> Result<i32> {
    match self {
      Self::Add(exp) => exp.eval(scopes),
      Self::RelAdd(lhs, op, rhs) => {
        let lhs = lhs.eval(scopes)?;
        let rhs = rhs.eval(scopes)?;
        Ok(match op {
          RelOp::Lt => lhs < rhs,
          RelOp::Gt => lhs > rhs,
          RelOp::Le => lhs <= rhs,
          RelOp::Ge => lhs >= rhs,
        } as i32)
      }
    }
  }
}

impl Evaluate for EqExp {
  fn eval(&self, scopes: &Scopes) -> Result<i32> {
    match self {
      Self::Rel(exp) => exp.eval(scopes),
      Self::EqRel(lhs, op, rhs) => {
        let lhs = lhs.eval(scopes)?;
        let rhs = rhs.eval(scopes)?;
        Ok(match op {
          EqOp::Eq => lhs == rhs,
          EqOp::Neq => lhs != rhs,
        } as i32)
      }
    }
  }
}

impl Evaluate for LAndExp {
  fn eval(&self, scopes: &Scopes) -> Result<i32> {
    match self {
      Self::Eq(exp) => exp.eval(scopes),
      Self::LAndEq(lhs, rhs) => Ok((lhs.eval(scopes)? != 0 && rhs.eval(scopes)? != 0) as i32),
    }
  }
}

impl Evaluate for LOrExp {
  fn eval(&self, scopes: &Scopes) -> Result<i32> {
    match self {
      Self::LAnd(exp) => exp.eval(scopes),
      Self::LOrLAnd(lhs, rhs) => Ok((lhs.eval(scopes)? != 0 || rhs.eval(scopes)? != 0) as i32),
    }
  }
}
