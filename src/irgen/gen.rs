use super::eval::Evaluate;
use super::func::FunctionInfo;
use super::scopes::{cur_func, cur_func_mut, Scopes};
use super::values::{ExpValue, Initializer, Value};
use super::{DimsToType, Error, Result};
use crate::ast::*;
use koopa::ir::builder_traits::*;
use koopa::ir::{BinaryOp, FunctionData, Program, Type, TypeKind};

/// Trait for generating Koopa IR program.
pub trait GenerateProgram<'ast> {
  type Out;

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out>;
}

impl<'ast> GenerateProgram<'ast> for CompUnit {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    let mut new_decl = |name, params_ty, ret_ty| {
      scopes
        .new_func(
          name,
          program.new_func(FunctionData::new_decl(
            format!("@{}", name),
            params_ty,
            ret_ty,
          )),
        )
        .unwrap();
    };
    // generate SysY library function declarations
    new_decl("getint", vec![], Type::get_i32());
    new_decl("getch", vec![], Type::get_i32());
    new_decl(
      "getarray",
      vec![Type::get_pointer(Type::get_i32())],
      Type::get_i32(),
    );
    new_decl("putint", vec![Type::get_i32()], Type::get_unit());
    new_decl("putch", vec![Type::get_i32()], Type::get_unit());
    new_decl(
      "putarray",
      vec![Type::get_i32(), Type::get_pointer(Type::get_i32())],
      Type::get_unit(),
    );
    new_decl("starttime", vec![], Type::get_unit());
    new_decl("stoptime", vec![], Type::get_unit());
    // generate global items
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
    // generate type and initializer
    let ty = self.dims.to_type(scopes)?;
    let init = self.init.generate(program, scopes)?.reshape(&ty)?;
    // generate constant
    if ty.is_i32() {
      match init {
        Initializer::Const(num) => scopes.new_value(&self.id, Value::Const(num))?,
        _ => unreachable!(),
      }
    } else {
      let value = init.into_const(program, scopes)?;
      let value = if scopes.is_global() {
        program.new_value().global_alloc(value)
      } else {
        let info = cur_func!(scopes);
        let alloc = info.new_alloc(program, ty, Some(&self.id));
        let store = info.new_value(program).store(value, alloc);
        info.push_inst(program, store);
        alloc
      };
      // add to scope
      scopes.new_value(&self.id, Value::Value(value))?;
    }
    Ok(())
  }
}

impl<'ast> GenerateProgram<'ast> for ConstInitVal {
  type Out = Initializer;

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    Ok(match self {
      Self::Exp(exp) => Initializer::Const(exp.generate(program, scopes)?),
      Self::List(list) => Initializer::List(
        list
          .iter()
          .map(|v| v.generate(program, scopes))
          .collect::<Result<_>>()?,
      ),
    })
  }
}

impl<'ast> GenerateProgram<'ast> for VarDecl {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    for def in &self.defs {
      def.generate(program, scopes)?;
    }
    Ok(())
  }
}

impl<'ast> GenerateProgram<'ast> for VarDef {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    // generate type and initializer
    let ty = self.dims.to_type(scopes)?;
    let init = self
      .init
      .as_ref()
      .map(|i| i.generate(program, scopes)?.reshape(&ty))
      .transpose()?;
    // generate variable
    let value = if scopes.is_global() {
      let init = match init {
        Some(init) => init.into_const(program, scopes)?,
        None => program.new_value().zero_init(ty),
      };
      program.new_value().global_alloc(init)
    } else {
      let info = cur_func!(scopes);
      let alloc = info.new_alloc(program, ty, Some(&self.id));
      if let Some(init) = init {
        init.into_stores(program, scopes, alloc);
      }
      alloc
    };
    // add to scope
    scopes.new_value(&self.id, Value::Value(value))?;
    Ok(())
  }
}

impl<'ast> GenerateProgram<'ast> for InitVal {
  type Out = Initializer;

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    Ok(match self {
      Self::Exp(exp) => {
        if scopes.is_global() {
          Initializer::Const(exp.eval(scopes).ok_or(Error::FailedToEval)?)
        } else {
          Initializer::Value(exp.generate(program, scopes)?.into_int(program, scopes)?)
        }
      }
      Self::List(list) => Initializer::List(
        list
          .iter()
          .map(|v| v.generate(program, scopes))
          .collect::<Result<_>>()?,
      ),
    })
  }
}

impl<'ast> GenerateProgram<'ast> for FuncDef {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    // generate parameter types and return type
    let params_ty = self
      .params
      .iter()
      .map(|p| p.generate(program, scopes))
      .collect::<Result<Vec<_>>>()?;
    let ret_ty = self.ty.generate(program, scopes)?;
    // create new fucntion
    let mut data = FunctionData::new(format!("@{}", self.id), params_ty, ret_ty);
    // get parameter list
    let params = data.params().to_owned();
    // generate entry/end/cur block
    let entry = data.dfg_mut().new_bb().basic_block(Some("%entry".into()));
    let end = data.dfg_mut().new_bb().basic_block(Some("%end".into()));
    let cur = data.dfg_mut().new_bb().basic_block(None);
    let mut ret_val = None;
    // generate return value
    if matches!(self.ty, FuncType::Int) {
      let alloc = data.dfg_mut().new_value().alloc(Type::get_i32());
      data.dfg_mut().set_value_name(alloc, Some("%ret".into()));
      ret_val = Some(alloc);
    }
    // insert function to program and scope
    let func = program.new_func(data);
    scopes.new_func(&self.id, func)?;
    // update function information
    let mut info = FunctionInfo::new(func, entry, end, ret_val);
    info.push_bb(program, entry);
    if let Some(ret_val) = info.ret_val() {
      info.push_inst(program, ret_val);
    }
    info.push_bb(program, cur);
    // generate allocations for parameters
    scopes.enter();
    for (param, value) in self.params.iter().zip(params) {
      let ty = program.func(func).dfg().value(value).ty().clone();
      let alloc = info.new_alloc(program, ty, Some(&param.id));
      let store = info.new_value(program).store(value, alloc);
      info.push_inst(program, store);
      scopes.new_value(&param.id, Value::Value(alloc))?;
    }
    scopes.cur_func = Some(info);
    // generate function body
    self.block.generate(program, scopes)?;
    scopes.exit();
    // handle end basic block
    let mut info = scopes.cur_func.take().unwrap();
    info.seal_entry(program, cur);
    info.seal_func(program);
    Ok(())
  }
}

impl<'ast> GenerateProgram<'ast> for FuncType {
  type Out = Type;

  fn generate(&'ast self, _: &mut Program, _: &mut Scopes<'ast>) -> Result<Self::Out> {
    Ok(match self {
      Self::Void => Type::get_unit(),
      Self::Int => Type::get_i32(),
    })
  }
}

impl<'ast> GenerateProgram<'ast> for FuncFParam {
  type Out = Type;

  fn generate(&'ast self, _: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    Ok(match &self.dims {
      Some(dims) => Type::get_pointer(dims.to_type(scopes)?),
      None => Type::get_i32(),
    })
  }
}

impl<'ast> GenerateProgram<'ast> for Block {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    scopes.enter();
    for item in &self.items {
      item.generate(program, scopes)?;
    }
    scopes.exit();
    Ok(())
  }
}

impl<'ast> GenerateProgram<'ast> for BlockItem {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    match self {
      Self::Decl(decl) => decl.generate(program, scopes),
      Self::Stmt(stmt) => stmt.generate(program, scopes),
    }
  }
}

impl<'ast> GenerateProgram<'ast> for Stmt {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    match self {
      Self::Assign(s) => s.generate(program, scopes),
      Self::ExpStmt(s) => s.generate(program, scopes),
      Self::Block(s) => s.generate(program, scopes),
      Self::If(s) => s.generate(program, scopes),
      Self::While(s) => s.generate(program, scopes),
      Self::Break(s) => s.generate(program, scopes),
      Self::Continue(s) => s.generate(program, scopes),
      Self::Return(s) => s.generate(program, scopes),
    }
  }
}

impl<'ast> GenerateProgram<'ast> for Assign {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    // generate value and left-value pointer
    let exp = self
      .exp
      .generate(program, scopes)?
      .into_int(program, scopes)?;
    let lval = self.lval.generate(program, scopes)?.into_ptr()?;
    // generate store
    let info = cur_func!(scopes);
    let store = info.new_value(program).store(exp, lval);
    info.push_inst(program, store);
    Ok(())
  }
}

impl<'ast> GenerateProgram<'ast> for ExpStmt {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    if let Some(exp) = &self.exp {
      exp.generate(program, scopes)?;
    }
    Ok(())
  }
}

impl<'ast> GenerateProgram<'ast> for If {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    // generate condition
    let cond = self
      .cond
      .generate(program, scopes)?
      .into_int(program, scopes)?;
    // generate branch and then/else basic block
    let info = cur_func_mut!(scopes);
    let then_bb = info.new_bb(program, Some("%if_then"));
    let else_bb = info.new_bb(program, Some("%if_else"));
    let br = info.new_value(program).branch(cond, then_bb, else_bb);
    info.push_inst(program, br);
    info.push_bb(program, then_bb);
    // generate then statement
    self.then.generate(program, scopes)?;
    // generate jump and end basic block
    let info = cur_func_mut!(scopes);
    let end_bb = info.new_bb(program, Some("%if_end"));
    let jump = info.new_value(program).jump(end_bb);
    info.push_inst(program, jump);
    info.push_bb(program, else_bb);
    // generate else statement
    if let Some(else_then) = &self.else_then {
      else_then.generate(program, scopes)?;
    }
    // generate jump
    let info = cur_func_mut!(scopes);
    let jump = info.new_value(program).jump(end_bb);
    info.push_inst(program, jump);
    info.push_bb(program, end_bb);
    Ok(())
  }
}

impl<'ast> GenerateProgram<'ast> for While {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    // generate loop entry basic block
    let info = cur_func_mut!(scopes);
    let entry_bb = info.new_bb(program, Some("%while_entry"));
    let jump = info.new_value(program).jump(entry_bb);
    info.push_inst(program, jump);
    info.push_bb(program, entry_bb);
    // generate condition
    let cond = self
      .cond
      .generate(program, scopes)?
      .into_int(program, scopes)?;
    // generate branch and loop body/end basic block
    let info = cur_func_mut!(scopes);
    let body_bb = info.new_bb(program, Some("%while_body"));
    let end_bb = info.new_bb(program, Some("%while_end"));
    let br = info.new_value(program).branch(cond, body_bb, end_bb);
    info.push_inst(program, br);
    info.push_bb(program, body_bb);
    // generate loop body
    scopes.loop_info.push((entry_bb, end_bb));
    self.body.generate(program, scopes)?;
    scopes.loop_info.pop();
    // generate jump
    let info = cur_func_mut!(scopes);
    let jump = info.new_value(program).jump(entry_bb);
    info.push_inst(program, jump);
    info.push_bb(program, end_bb);
    Ok(())
  }
}

impl<'ast> GenerateProgram<'ast> for Break {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    // jump to the end of loop
    let info = &mut cur_func_mut!(scopes);
    let (_, end) = scopes.loop_info.last().ok_or(Error::NotInLoop)?;
    let jump = info.new_value(program).jump(*end);
    info.push_inst(program, jump);
    // push new basic block
    let next = info.new_bb(program, None);
    info.push_bb(program, next);
    Ok(())
  }
}

impl<'ast> GenerateProgram<'ast> for Continue {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    // jump to the entry of loop
    let info = &mut cur_func_mut!(scopes);
    let (entry, _) = scopes.loop_info.last().ok_or(Error::NotInLoop)?;
    let jump = info.new_value(program).jump(*entry);
    info.push_inst(program, jump);
    // push new basic block
    let next = info.new_bb(program, None);
    info.push_bb(program, next);
    Ok(())
  }
}

impl<'ast> GenerateProgram<'ast> for Return {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    if let Some(ret_val) = cur_func!(scopes).ret_val() {
      // generate store
      if let Some(val) = &self.exp {
        let value = val.generate(program, scopes)?.into_int(program, scopes)?;
        let info = cur_func!(scopes);
        let store = info.new_value(program).store(value, ret_val);
        info.push_inst(program, store);
      }
    } else if self.exp.is_some() {
      return Err(Error::RetValInVoidFunc);
    }
    // jump to the end basic block
    let info = &mut cur_func_mut!(scopes);
    let jump = info.new_value(program).jump(info.end());
    info.push_inst(program, jump);
    // push new basic block
    let next = info.new_bb(program, None);
    info.push_bb(program, next);
    Ok(())
  }
}

impl<'ast> GenerateProgram<'ast> for Exp {
  type Out = ExpValue;

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    self.lor.generate(program, scopes)
  }
}

impl<'ast> GenerateProgram<'ast> for LVal {
  type Out = ExpValue;

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    // handle constant
    let mut value = match scopes.value(&self.id)? {
      Value::Value(value) => *value,
      Value::Const(num) => {
        return if self.indices.is_empty() {
          let value = cur_func!(scopes).new_value(program).integer(*num);
          Ok(ExpValue::Int(value))
        } else {
          Err(Error::DerefInt)
        };
      }
    };
    // check type
    let mut is_ptr_ptr = false;
    let mut dims = match scopes.ty(program, value).kind() {
      TypeKind::Pointer(base) => {
        let mut ty = base;
        let mut dims = 0;
        loop {
          ty = match ty.kind() {
            TypeKind::Array(base, _) => base,
            TypeKind::Pointer(base) => {
              is_ptr_ptr = true;
              base
            }
            _ => break dims,
          };
          dims += 1;
        }
      }
      _ => 0,
    };
    // generate load for array parameter
    if is_ptr_ptr {
      let info = cur_func!(scopes);
      value = info.new_value(program).load(value);
      info.push_inst(program, value);
    }
    // handle array dereference
    for (i, index) in self.indices.iter().enumerate() {
      // check if dereferencing integer
      if dims == 0 {
        return Err(Error::DerefInt);
      }
      dims -= 1;
      // generate index
      let index = index.generate(program, scopes)?.into_val(program, scopes)?;
      // generate pointer calculation
      let info = cur_func!(scopes);
      value = if is_ptr_ptr && i == 0 {
        info.new_value(program).get_ptr(value, index)
      } else {
        info.new_value(program).get_elem_ptr(value, index)
      };
      info.push_inst(program, value);
    }
    // generate pointer calculation for function arguments
    if dims == 0 {
      Ok(ExpValue::IntPtr(value))
    } else {
      if !is_ptr_ptr {
        let info = cur_func!(scopes);
        let zero = info.new_value(program).integer(0);
        value = info.new_value(program).get_elem_ptr(value, zero);
        info.push_inst(program, value);
      }
      Ok(ExpValue::ArrPtr(value))
    }
  }
}

impl<'ast> GenerateProgram<'ast> for PrimaryExp {
  type Out = ExpValue;

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    match self {
      Self::Exp(exp) => exp.generate(program, scopes),
      Self::LVal(lval) => lval.generate(program, scopes),
      Self::Number(num) => Ok(ExpValue::Int(
        cur_func!(scopes).new_value(program).integer(*num),
      )),
    }
  }
}

impl<'ast> GenerateProgram<'ast> for UnaryExp {
  type Out = ExpValue;

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    match self {
      Self::Primary(exp) => exp.generate(program, scopes),
      Self::Call(call) => call.generate(program, scopes),
      Self::Unary(op, exp) => {
        let exp = exp.generate(program, scopes)?.into_int(program, scopes)?;
        let info = cur_func!(scopes);
        let zero = info.new_value(program).integer(0);
        let value = match op {
          UnaryOp::Neg => info.new_value(program).binary(BinaryOp::Sub, zero, exp),
          UnaryOp::LNot => info.new_value(program).binary(BinaryOp::Eq, exp, zero),
        };
        info.push_inst(program, value);
        Ok(ExpValue::Int(value))
      }
    }
  }
}

impl<'ast> GenerateProgram<'ast> for FuncCall {
  type Out = ExpValue;

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    // get function from scope
    let func = scopes.func(&self.id)?;
    // get function type
    let (params_ty, is_void) = match program.func(func).ty().kind() {
      TypeKind::Function(params, ret) => (params.clone(), ret.is_unit()),
      _ => unreachable!(),
    };
    // generate arguments
    let args = self
      .args
      .iter()
      .map(|a| a.generate(program, scopes)?.into_val(program, scopes))
      .collect::<Result<Vec<_>>>()?;
    // check argument types
    if params_ty.len() != args.len() {
      return Err(Error::ArgMismatch);
    }
    for (param_ty, arg) in params_ty.iter().zip(&args) {
      if param_ty != &scopes.ty(program, *arg) {
        return Err(Error::ArgMismatch);
      }
    }
    // generate function call
    let info = cur_func!(scopes);
    let call = info.new_value(program).call(func, args);
    info.push_inst(program, call);
    // return value if not void
    if is_void {
      Ok(ExpValue::Void)
    } else {
      Ok(ExpValue::Int(call))
    }
  }
}

impl<'ast> GenerateProgram<'ast> for MulExp {
  type Out = ExpValue;

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    match self {
      Self::Unary(exp) => exp.generate(program, scopes),
      Self::MulUnary(lhs, op, rhs) => {
        let lhs = lhs.generate(program, scopes)?.into_int(program, scopes)?;
        let rhs = rhs.generate(program, scopes)?.into_int(program, scopes)?;
        let op = op.generate(program, scopes)?;
        let info = cur_func!(scopes);
        let value = info.new_value(program).binary(op, lhs, rhs);
        info.push_inst(program, value);
        Ok(ExpValue::Int(value))
      }
    }
  }
}

impl<'ast> GenerateProgram<'ast> for AddExp {
  type Out = ExpValue;

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    match self {
      Self::Mul(exp) => exp.generate(program, scopes),
      Self::AddMul(lhs, op, rhs) => {
        let lhs = lhs.generate(program, scopes)?.into_int(program, scopes)?;
        let rhs = rhs.generate(program, scopes)?.into_int(program, scopes)?;
        let op = op.generate(program, scopes)?;
        let info = cur_func!(scopes);
        let value = info.new_value(program).binary(op, lhs, rhs);
        info.push_inst(program, value);
        Ok(ExpValue::Int(value))
      }
    }
  }
}

impl<'ast> GenerateProgram<'ast> for RelExp {
  type Out = ExpValue;

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    match self {
      Self::Add(exp) => exp.generate(program, scopes),
      Self::RelAdd(lhs, op, rhs) => {
        let lhs = lhs.generate(program, scopes)?.into_int(program, scopes)?;
        let rhs = rhs.generate(program, scopes)?.into_int(program, scopes)?;
        let op = op.generate(program, scopes)?;
        let info = cur_func!(scopes);
        let value = info.new_value(program).binary(op, lhs, rhs);
        info.push_inst(program, value);
        Ok(ExpValue::Int(value))
      }
    }
  }
}

impl<'ast> GenerateProgram<'ast> for EqExp {
  type Out = ExpValue;

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    match self {
      Self::Rel(exp) => exp.generate(program, scopes),
      Self::EqRel(lhs, op, rhs) => {
        let lhs = lhs.generate(program, scopes)?.into_int(program, scopes)?;
        let rhs = rhs.generate(program, scopes)?.into_int(program, scopes)?;
        let op = op.generate(program, scopes)?;
        let info = cur_func!(scopes);
        let value = info.new_value(program).binary(op, lhs, rhs);
        info.push_inst(program, value);
        Ok(ExpValue::Int(value))
      }
    }
  }
}

/// Generates logical operators.
macro_rules! generate_logical_ops {
  (
    $lhs:expr, $rhs:expr, $program:expr, $scopes:expr,
    $prefix:literal, $rhs_bb:ident, $end_bb:ident, $tbb:ident, $fbb:ident
  ) => {{
    // generate result
    let result = cur_func!($scopes).new_alloc($program, Type::get_i32(), None);
    // generate left-hand side expression
    let lhs = $lhs
      .generate($program, $scopes)?
      .into_int($program, $scopes)?;
    let info = cur_func_mut!($scopes);
    let zero = info.new_value($program).integer(0);
    let lhs = info.new_value($program).binary(BinaryOp::NotEq, lhs, zero);
    info.push_inst($program, lhs);
    let store = info.new_value($program).store(lhs, result);
    info.push_inst($program, store);
    // generate basic blocks and branch
    let $rhs_bb = info.new_bb($program, Some(concat!("%", $prefix, "_rhs")));
    let $end_bb = info.new_bb($program, Some(concat!("%", $prefix, "_end")));
    let br = info.new_value($program).branch(lhs, $tbb, $fbb);
    info.push_inst($program, br);
    // generate right-hand side expression
    info.push_bb($program, $rhs_bb);
    let rhs = $rhs
      .generate($program, $scopes)?
      .into_int($program, $scopes)?;
    let info = cur_func_mut!($scopes);
    let rhs = info.new_value($program).binary(BinaryOp::NotEq, rhs, zero);
    info.push_inst($program, rhs);
    let store = info.new_value($program).store(rhs, result);
    info.push_inst($program, store);
    // generate jump
    let jump = info.new_value($program).jump($end_bb);
    info.push_inst($program, jump);
    info.push_bb($program, $end_bb);
    // generate load
    let load = info.new_value($program).load(result);
    info.push_inst($program, load);
    Ok(ExpValue::Int(load))
  }};
}

impl<'ast> GenerateProgram<'ast> for LAndExp {
  type Out = ExpValue;

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    match self {
      Self::Eq(exp) => exp.generate(program, scopes),
      Self::LAndEq(lhs, rhs) => generate_logical_ops! {
        lhs, rhs, program, scopes, "land", rhs_bb, end_bb, rhs_bb, end_bb
      },
    }
  }
}

impl<'ast> GenerateProgram<'ast> for LOrExp {
  type Out = ExpValue;

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    match self {
      Self::LAnd(exp) => exp.generate(program, scopes),
      Self::LOrLAnd(lhs, rhs) => generate_logical_ops! {
        lhs, rhs, program, scopes, "lor", rhs_bb, end_bb, end_bb, rhs_bb
      },
    }
  }
}

impl<'ast> GenerateProgram<'ast> for ConstExp {
  type Out = i32;

  fn generate(&'ast self, _: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    self.eval(scopes).ok_or(Error::FailedToEval)
  }
}

impl<'ast> GenerateProgram<'ast> for MulOp {
  type Out = BinaryOp;

  fn generate(&'ast self, _: &mut Program, _: &mut Scopes<'ast>) -> Result<Self::Out> {
    Ok(match self {
      MulOp::Mul => BinaryOp::Mul,
      MulOp::Div => BinaryOp::Div,
      MulOp::Mod => BinaryOp::Mod,
    })
  }
}

impl<'ast> GenerateProgram<'ast> for AddOp {
  type Out = BinaryOp;

  fn generate(&'ast self, _: &mut Program, _: &mut Scopes<'ast>) -> Result<Self::Out> {
    Ok(match self {
      AddOp::Add => BinaryOp::Add,
      AddOp::Sub => BinaryOp::Sub,
    })
  }
}

impl<'ast> GenerateProgram<'ast> for RelOp {
  type Out = BinaryOp;

  fn generate(&'ast self, _: &mut Program, _: &mut Scopes<'ast>) -> Result<Self::Out> {
    Ok(match self {
      RelOp::Lt => BinaryOp::Lt,
      RelOp::Gt => BinaryOp::Gt,
      RelOp::Le => BinaryOp::Le,
      RelOp::Ge => BinaryOp::Ge,
    })
  }
}

impl<'ast> GenerateProgram<'ast> for EqOp {
  type Out = BinaryOp;

  fn generate(&'ast self, _: &mut Program, _: &mut Scopes<'ast>) -> Result<Self::Out> {
    Ok(match self {
      EqOp::Eq => BinaryOp::Eq,
      EqOp::Neq => BinaryOp::NotEq,
    })
  }
}
