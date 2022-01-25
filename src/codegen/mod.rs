use koopa::ir::entities::{BasicBlockData, ValueData};
use koopa::ir::{BasicBlock, Function, FunctionData, Program, Type, Value};
use std::collections::HashMap;
use std::fs::File;
use std::io::Result;

/// Generates the given Koopa IR program to RISC-V assembly.
pub fn generate_asm(program: &Program, path: &str) -> Result<()> {
  Type::set_ptr_size(4);
  program.generate(&mut File::create(path)?, &mut ProgramInfo::new(program))
}

/// Some necessary information during assembly generation.
struct ProgramInfo<'p> {
  program: &'p Program,
  values: HashMap<Value, String>,
  funcs: HashMap<Function, &'p str>,
  cur_func: Option<FunctionInfo>,
}

/// Returns a reference to the current function information.
macro_rules! cur_func {
  ($info:expr) => {
    $info.cur_func.as_ref().unwrap()
  };
}

/// Returns a mutable reference to the current function information.
macro_rules! cur_func_mut {
  ($info:expr) => {
    $info.cur_func.as_mut().unwrap()
  };
}

impl<'p> ProgramInfo<'p> {
  /// Creates a new program information.
  fn new(program: &'p Program) -> Self {
    Self {
      program,
      values: HashMap::new(),
      funcs: HashMap::new(),
      cur_func: None,
    }
  }

  /// Returns `true` if is currently generating global items.
  fn is_global(&self) -> bool {
    self.cur_func.is_none()
  }
}

/// Function information.
struct FunctionInfo {
  slot_size: usize,
  values: HashMap<Value, usize>,
  bbs: HashMap<BasicBlock, String>,
}

impl FunctionInfo {
  /// Creates a new function information.
  fn new() -> Self {
    Self {
      slot_size: 0,
      values: HashMap::new(),
      bbs: HashMap::new(),
    }
  }

  /// Creates a new slot for the given allocation.
  fn new_slot(&mut self, alloc: Value, ty: &Type) {
    self.values.insert(alloc, self.slot_size);
    self.slot_size += ty.size();
  }
}

/// A global/local value.
enum AsmValue<'i> {
  Global(&'i str),
  Local(usize),
}

/// Trait for generating RISC-V assembly.
trait GenerateAsm<'p, 'i> {
  type Out;

  fn generate(&self, f: &mut File, info: &'i mut ProgramInfo<'p>) -> Result<Self::Out>;
}

impl<'p, 'i> GenerateAsm<'p, 'i> for Program {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    for value in self.inst_layout() {
      self.borrow_value(*value).generate(f, info)?;
    }
    for func in self.func_layout() {
      self.func(*func).generate(f, info)?;
    }
    Ok(())
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for Function {
  type Out = &'p str;

  fn generate(&self, _: &mut File, info: &mut ProgramInfo<'p>) -> Result<Self::Out> {
    Ok(
      info
        .funcs
        .entry(*self)
        .or_insert_with(|| info.program.func(*self).name()),
    )
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for FunctionData {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    // update function information
    let func = FunctionInfo::new();
    // generate basic blocks
    todo!()
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for BasicBlock {
  type Out = &'i str;

  fn generate(&self, _: &mut File, info: &'i mut ProgramInfo) -> Result<Self::Out> {
    Ok(cur_func!(info).bbs.get(self).as_ref().unwrap())
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for BasicBlockData {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    todo!()
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for Value {
  type Out = AsmValue<'i>;

  fn generate(&self, _: &mut File, info: &'i mut ProgramInfo) -> Result<Self::Out> {
    if self.is_global() {
      Ok(AsmValue::Global(info.values.entry(*self).or_insert_with(
        || {
          info
            .program
            .borrow_value(*self)
            .name()
            .as_ref()
            .unwrap()
            .into()
        },
      )))
    } else {
      Ok(AsmValue::Local(*cur_func!(info).values.get(self).unwrap()))
    }
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for ValueData {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    todo!()
  }
}
