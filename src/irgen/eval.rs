use super::scopes::Scopes;
use super::values::Value;
use crate::ast::*;

/// Trait for evaluating constant.
pub trait Evaluate {
  fn eval(&self, scopes: &Scopes) -> Option<i32>;
}

impl Evaluate for Exp {
  fn eval(&self, scopes: &Scopes) -> Option<i32> {
    self.lor.eval(scopes)
  }
}

impl Evaluate for LVal {
  fn eval(&self, scopes: &Scopes) -> Option<i32> {
    let val = scopes.value(&self.id).ok()?;
    if self.indices.is_empty() {
      match val {
        Value::Const(i) => Some(*i),
        _ => None,
      }
    } else {
      None
    }
  }
}

impl Evaluate for PrimaryExp {
  fn eval(&self, scopes: &Scopes) -> Option<i32> {
    match self {
      Self::Exp(exp) => exp.eval(scopes),
      Self::LVal(lval) => lval.eval(scopes),
      Self::Number(num) => Some(*num),
    }
  }
}

impl Evaluate for UnaryExp {
  fn eval(&self, scopes: &Scopes) -> Option<i32> {
    match self {
      Self::Primary(primary) => primary.eval(scopes),
      Self::Call(_) => None,
      Self::Unary(op, exp) => exp.eval(scopes).map(|exp| match op {
        UnaryOp::Neg => -exp,
        UnaryOp::LNot => (exp == 0) as i32,
      }),
    }
  }
}

impl Evaluate for MulExp {
  fn eval(&self, scopes: &Scopes) -> Option<i32> {
    match self {
      Self::Unary(exp) => exp.eval(scopes),
      Self::MulUnary(lhs, op, rhs) => match (lhs.eval(scopes), rhs.eval(scopes)) {
        (Some(lhs), Some(rhs)) => match op {
          MulOp::Mul => Some(lhs * rhs),
          MulOp::Div => (rhs != 0).then_some(lhs / rhs),
          MulOp::Mod => (rhs != 0).then_some(lhs % rhs),
        },
        _ => None,
      },
    }
  }
}

impl Evaluate for AddExp {
  fn eval(&self, scopes: &Scopes) -> Option<i32> {
    match self {
      Self::Mul(exp) => exp.eval(scopes),
      Self::AddMul(lhs, op, rhs) => match (lhs.eval(scopes), rhs.eval(scopes)) {
        (Some(lhs), Some(rhs)) => Some(match op {
          AddOp::Add => lhs + rhs,
          AddOp::Sub => lhs - rhs,
        }),
        _ => None,
      },
    }
  }
}

impl Evaluate for RelExp {
  fn eval(&self, scopes: &Scopes) -> Option<i32> {
    match self {
      Self::Add(exp) => exp.eval(scopes),
      Self::RelAdd(lhs, op, rhs) => match (lhs.eval(scopes), rhs.eval(scopes)) {
        (Some(lhs), Some(rhs)) => Some(match op {
          RelOp::Lt => (lhs < rhs) as i32,
          RelOp::Gt => (lhs > rhs) as i32,
          RelOp::Le => (lhs <= rhs) as i32,
          RelOp::Ge => (lhs >= rhs) as i32,
        }),
        _ => None,
      },
    }
  }
}

impl Evaluate for EqExp {
  fn eval(&self, scopes: &Scopes) -> Option<i32> {
    match self {
      Self::Rel(exp) => exp.eval(scopes),
      Self::EqRel(lhs, op, rhs) => match (lhs.eval(scopes), rhs.eval(scopes)) {
        (Some(lhs), Some(rhs)) => Some(match op {
          EqOp::Eq => (lhs == rhs) as i32,
          EqOp::Neq => (lhs != rhs) as i32,
        }),
        _ => None,
      },
    }
  }
}

impl Evaluate for LAndExp {
  fn eval(&self, scopes: &Scopes) -> Option<i32> {
    match self {
      Self::Eq(exp) => exp.eval(scopes),
      Self::LAndEq(lhs, rhs) => match (lhs.eval(scopes), rhs.eval(scopes)) {
        (Some(lhs), Some(rhs)) => Some((lhs != 0 && rhs != 0) as i32),
        _ => None,
      },
    }
  }
}

impl Evaluate for LOrExp {
  fn eval(&self, scopes: &Scopes) -> Option<i32> {
    match self {
      Self::LAnd(exp) => exp.eval(scopes),
      Self::LOrLAnd(lhs, rhs) => match (lhs.eval(scopes), rhs.eval(scopes)) {
        (Some(lhs), Some(rhs)) => Some((lhs != 0 || rhs != 0) as i32),
        _ => None,
      },
    }
  }
}

impl Evaluate for ConstExp {
  fn eval(&self, scopes: &Scopes) -> Option<i32> {
    self.exp.eval(scopes)
  }
}
