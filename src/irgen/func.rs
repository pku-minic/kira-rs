use koopa::ir::Value;
use koopa::ir::{builder::LocalBuilder, builder_traits::*};
use koopa::ir::{BasicBlock, Function, Program, Type};

/// Function information.
pub struct FunctionInfo {
  func: Function,
  entry: BasicBlock,
  end: BasicBlock,
  cur: BasicBlock,
  ret_val: Option<Value>,
}

impl FunctionInfo {
  /// Creates a new function information.
  pub fn new(func: Function, entry: BasicBlock, end: BasicBlock, ret_val: Option<Value>) -> Self {
    Self {
      func,
      entry,
      end,
      cur: entry,
      ret_val,
    }
  }

  /// Returns the curren function.
  pub fn func(&self) -> Function {
    self.func
  }

  /// Returns the end basic block.
  pub fn end(&self) -> BasicBlock {
    self.end
  }

  /// Returns the return value.
  pub fn ret_val(&self) -> Option<Value> {
    self.ret_val
  }

  /// Creates a new basic block in function.
  pub fn new_bb(&self, program: &mut Program, name: Option<&str>) -> BasicBlock {
    program
      .func_mut(self.func)
      .dfg_mut()
      .new_bb()
      .basic_block(name.map(|s| s.into()))
  }

  /// Creates a new value in function.
  pub fn new_value<'p>(&self, program: &'p mut Program) -> LocalBuilder<'p> {
    program.func_mut(self.func).dfg_mut().new_value()
  }

  /// Pushes the basic block to the function,
  /// updates the current basic block.
  pub fn push_bb(&mut self, program: &mut Program, bb: BasicBlock) {
    program
      .func_mut(self.func)
      .layout_mut()
      .bbs_mut()
      .push_key_back(bb)
      .unwrap();
    self.cur = bb;
  }

  /// Pushes the instruction to the back of the given basic block.
  pub fn push_inst_to(&self, program: &mut Program, bb: BasicBlock, inst: Value) {
    program
      .func_mut(self.func)
      .layout_mut()
      .bb_mut(bb)
      .insts_mut()
      .push_key_back(inst)
      .unwrap();
  }

  /// Pushes the instruction to the back of the current basic block.
  pub fn push_inst(&self, program: &mut Program, inst: Value) {
    self.push_inst_to(program, self.cur, inst);
  }

  /// Creates a new allocation and inserts to the entry block.
  pub fn new_alloc(&self, program: &mut Program, ty: Type, name: Option<&str>) -> Value {
    let alloc = self.new_value(program).alloc(ty);
    if let Some(name) = name {
      let name = if name.len() <= 512 {
        format!("@{}", name)
      } else {
        format!("@{}", &name[..512])
      };
      program
        .func_mut(self.func)
        .dfg_mut()
        .set_value_name(alloc, Some(name));
    }
    self.push_inst_to(program, self.entry, alloc);
    alloc
  }

  /// Seals the entry block.
  pub fn seal_entry(&self, program: &mut Program, next: BasicBlock) {
    let jump = self.new_value(program).jump(next);
    self.push_inst_to(program, self.entry, jump);
  }

  /// Seals the function.
  pub fn seal_func(&mut self, program: &mut Program) {
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
