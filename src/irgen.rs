use crate::ast::*;
use koopa::ir::Value as IrValue;
use koopa::ir::{builder::LocalBuilder, builder_traits::*};
use koopa::ir::{BasicBlock, BinaryOp, Function, FunctionData, Program, Type, TypeKind};
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

  /// Returns type of the given value.
  fn ty(&self, program: &Program, value: IrValue) -> Type {
    if value.is_global() {
      program.borrow_value(value).ty().clone()
    } else {
      program
        .func(cur_func!(self).func)
        .dfg()
        .value(value)
        .ty()
        .clone()
    }
  }
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
  fn new_value<'p>(&self, program: &'p mut Program) -> LocalBuilder<'p> {
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
  fn new_alloc(&self, program: &mut Program, ty: Type) -> IrValue {
    let alloc = self.new_value(program).alloc(ty);
    self.push_inst_to(program, self.entry, alloc);
    alloc
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

/// An initializer.
enum Initializer {
  Value(IrValue),
  List(Vec<Initializer>),
}

impl Initializer {
  //
}

/// An expression value.
enum ExpValue {
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
  fn into_val(self, program: &mut Program, scopes: &Scopes) -> Result<IrValue> {
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
  fn into_int(self, program: &mut Program, scopes: &Scopes) -> Result<IrValue> {
    match self {
      Self::ArrPtr(_) => Err(Error::NonIntCalc),
      _ => self.into_val(program, scopes),
    }
  }

  /// Converts the value into a left-value pointer.
  fn into_ptr(self) -> Result<IrValue> {
    match self {
      Self::IntPtr(ptr) => Ok(ptr),
      Self::ArrPtr(_) => Err(Error::ArrayAssign),
      _ => unreachable!(),
    }
  }
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
    // generate type and initializer
    let ty = self.dims.to_type(scopes)?;
    let init = self.init.generate(program, scopes)?;
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for ConstInitVal {
  type Out = Initializer;

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    Ok(match self {
      Self::Exp(exp) => {
        let value = exp.generate(program, scopes)?;
        Initializer::Value(cur_func!(scopes).new_value(program).integer(value))
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
    // generate type
    let ty = self.dims.to_type(scopes)?;
    todo!()
  }
}

impl<'ast> GenerateProgram<'ast> for InitVal {
  type Out = Initializer;

  fn generate(&'ast self, program: &mut Program, scopes: &mut Scopes<'ast>) -> Result<Self::Out> {
    Ok(match self {
      Self::Exp(exp) => Initializer::Value(if scopes.is_global() {
        let value = exp.eval(scopes).ok_or(Error::FailedToEval)?;
        program.new_value().integer(value)
      } else {
        exp.generate(program, scopes)?.into_int(program, scopes)?
      }),
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
    let mut data = FunctionData::new(self.id.clone(), params_ty, ret_ty);
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
    if let Some(ret_val) = &info.ret_val {
      info.push_inst(program, *ret_val);
    }
    info.push_bb(program, cur);
    // generate allocations for parameters
    scopes.enter();
    for (param, value) in self.params.iter().zip(params) {
      let ty = program.func(func).dfg().value(value).ty().clone();
      let alloc = info.new_alloc(program, ty);
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
    if let Some(ret_val) = cur_func!(scopes).ret_val {
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
    let jump = info.new_value(program).jump(info.end);
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
      if self.indices.is_empty() && !is_ptr_ptr {
        let info = cur_func!(scopes);
        let zero = info.new_value(program).integer(0);
        value = info.new_value(program).get_ptr(value, zero);
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
    let result = cur_func!($scopes).new_alloc($program, Type::get_i32());
    // generate left-hand side expression
    let lhs = $lhs
      .generate($program, $scopes)?
      .into_int($program, $scopes)?;
    let info = cur_func_mut!($scopes);
    let zero = info.new_value($program).integer(0);
    let lhs = info.new_value($program).binary(BinaryOp::NotEq, lhs, zero);
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

/// Helper trait for converting dimentions to type.
trait DimsToType {
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
