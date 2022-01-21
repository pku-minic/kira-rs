use crate::ast::*;
use koopa::ir::Value as IrValue;
use koopa::ir::{builder::LocalBuilder, builder_traits::*};
use koopa::ir::{BasicBlock, BinaryOp, Function, FunctionData, Program, Type};
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
  cur_func: Option<FunctionInfo>,
  loop_info: Vec<(BasicBlock, BasicBlock)>,
}

impl<'ast> Scopes<'ast> {
  /// Creates a new `Scopes`.
  fn new() -> Self {
    Self {
      vals: vec![HashMap::new()],
      funcs: HashMap::new(),
      cur_func: None,
      loop_info: Vec::new(),
    }
  }

  /// Returns `true` if is currently in global scope.
  fn is_global(&self) -> bool {
    self.cur_func.is_none()
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

  /// Enters a new scope.
  fn enter(&mut self) {
    self.vals.push(HashMap::new());
  }

  /// Exits from the current scope.
  fn exit(&mut self) {
    self.vals.pop();
  }
}

/// Returns a reference to the current function information.
macro_rules! cur_func {
  ($scopes:expr) => {
    $scopes.cur_func.as_ref().unwrap()
  };
}

/// Returns a mutable reference to the current function information.
macro_rules! cur_func_mut {
  ($scopes:expr) => {
    $scopes.cur_func.as_mut().unwrap()
  };
}

/// Function information.
struct FunctionInfo {
  func: Function,
  entry: BasicBlock,
  end: BasicBlock,
  cur: BasicBlock,
  ret_val: Option<IrValue>,
}

impl FunctionInfo {
  /// Creates a new function information.
  fn new(func: Function, entry: BasicBlock, end: BasicBlock, ret_val: Option<IrValue>) -> Self {
    Self {
      func,
      entry,
      end,
      cur: entry,
      ret_val,
    }
  }

  /// Creates a new basic block in function.
  fn new_bb(&self, program: &mut Program, name: Option<&str>) -> BasicBlock {
    program
      .func_mut(self.func)
      .dfg_mut()
      .new_bb()
      .basic_block(name.map(|s| s.into()))
  }

  /// Creates a new value in function.
  fn new_value<'func>(&self, program: &'func mut Program) -> LocalBuilder<'func> {
    program.func_mut(self.func).dfg_mut().new_value()
  }

  /// Pushes the basic block to the function,
  /// updates the current basic block.
  fn push_bb(&mut self, program: &mut Program, bb: BasicBlock) {
    program
      .func_mut(self.func)
      .layout_mut()
      .bbs_mut()
      .push_key_back(bb)
      .unwrap();
    self.cur = bb;
  }

  /// Pushes the instruction to the back of the given basic block.
  fn push_inst_to(&self, program: &mut Program, bb: BasicBlock, inst: IrValue) {
    program
      .func_mut(self.func)
      .layout_mut()
      .bb_mut(bb)
      .insts_mut()
      .push_key_back(inst)
      .unwrap();
  }

  /// Pushes the instruction to the back of the current basic block.
  fn push_inst(&self, program: &mut Program, inst: IrValue) {
    self.push_inst_to(program, self.cur, inst);
  }

  /// Creates a new allocation and inserts to the entry block.
  fn new_alloc(&self, program: &mut Program, ty: Type) -> Value {
    let alloc = self.new_value(program).alloc(ty);
    self.push_inst_to(program, self.entry, alloc);
    Value::Value(alloc)
  }

  /// Seals the entry block.
  fn seal_entry(&self, program: &mut Program, next: BasicBlock) {
    let jump = self.new_value(program).jump(next);
    self.push_inst_to(program, self.entry, jump);
  }

  /// Seals the function.
  fn seal_func(&mut self, program: &mut Program) {
    // jump to the end basic block
    let jump = self.new_value(program).jump(self.end);
    self.push_inst(program, jump);
    // push the end basic block
    self.push_bb(program, self.end);
    // generate return
    let value = self.ret_val.map(|alloc| {
      let value = self.new_value(program).load(alloc);
      self.push_inst(program, value);
      value
    });
    let ret = self.new_value(program).ret(value);
    self.push_inst(program, ret);
  }
}

/// A value.
enum Value {
  /// Koopa IR value.
  Value(IrValue),
  /// Constant integer.
  Const(i32),
}

/// Error returned by IR generator.
pub enum Error {
  DuplicatedDef,
  SymbolNotFound,
  FailedToEval,
  InvalidArrayLen,
  NotInLoop,
  RetValInVoidFunc,
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::DuplicatedDef => write!(f, "duplicated symbol definition"),
      Self::SymbolNotFound => write!(f, "symbol not found"),
      Self::FailedToEval => write!(f, "failed to evaluate constant"),
      Self::InvalidArrayLen => write!(f, "invalid array length"),
      Self::NotInLoop => write!(f, "using break/continue outside of loop"),
      Self::RetValInVoidFunc => write!(f, "returning value in void fucntion"),
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

/// Trait for generating Koopa IR program.
trait GenerateProgram<'ast> {
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
          program.new_func(FunctionData::new_decl(name.into(), params_ty, ret_ty)),
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
    for def in &self.defs {
      def.generate(program, scopes)?;
    }
    Ok(())
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
    // generate parameter types and return type
    let params_ty = self
      .params
      .iter()
      .map(|p| p.generate(program, scopes))
      .collect::<Result<Vec<_>>>()?;
    let ret_ty = self.ty.generate(program, scopes)?;
    // create new fucntion
    let mut data = FunctionData::new(self.id.clone(), params_ty, ret_ty);
    // add parameters to scope
    scopes.enter();
    for (param, value) in self.params.iter().zip(data.params()) {
      scopes.new_value(&param.id, Value::Value(*value))?;
    }
    // generate entry/end/cur block and return value
    let entry = data.dfg_mut().new_bb().basic_block(Some("%entry".into()));
    let end = data.dfg_mut().new_bb().basic_block(Some("%end".into()));
    let cur = data.dfg_mut().new_bb().basic_block(None);
    let mut ret_val = None;
    if matches!(self.ty, FuncType::Int) {
      ret_val = Some(data.dfg_mut().new_value().alloc(Type::get_i32()));
    }
    // insert function to program and scope
    let func = program.new_func(data);
    scopes.new_func(&self.id, func)?;
    // update function information
    let mut info = FunctionInfo::new(func, entry, end, ret_val);
    info.push_bb(program, entry);
    info.push_bb(program, cur);
    if let Some(ret_val) = &info.ret_val {
      info.push_inst_to(program, entry, *ret_val);
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

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    Ok(match &self.dims {
      Some(dims) => Type::get_pointer(dims.iter().rev().fold(Ok(Type::get_i32()), |b, exp| {
        let base = b?;
        let len = exp.generate(program, scopes)?;
        (len >= 1)
          .then(|| Type::get_array(base, len as usize))
          .ok_or(Error::InvalidArrayLen)
      })?),
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
    todo!()
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
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for While {
  type Out = ();

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    todo!()
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
    // jump to the begin of loop
    let info = &mut cur_func_mut!(scopes);
    let (begin, _) = scopes.loop_info.last().ok_or(Error::NotInLoop)?;
    let jump = info.new_value(program).jump(*begin);
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
    if let Some(ret_val) = cur_func!(scopes).ret_val {
      // generate store
      if let Some(val) = &self.exp {
        let value = val.generate(program, scopes)?;
        let info = &cur_func!(scopes);
        let store = info.new_value(program).store(value, ret_val);
        info.push_inst(program, store);
      }
    } else if self.exp.is_some() {
      return Err(Error::RetValInVoidFunc);
    }
    // jump to the end basic block
    let info = &mut cur_func_mut!(scopes);
    let jump = info.new_value(program).jump(info.end);
    info.push_inst(program, jump);
    // push new basic block
    let next = info.new_bb(program, None);
    info.push_bb(program, next);
    Ok(())
  }
}

impl<'ast> GenerateProgram<'ast> for Exp {
  type Out = IrValue;

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

/// Trait for evaluating constant.
trait Evaluate {
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
    if self.dims.is_empty() {
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
          MulOp::Div => (rhs != 0).then(|| lhs / rhs),
          MulOp::Mod => (rhs != 0).then(|| lhs / rhs),
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
