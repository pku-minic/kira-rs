mod builder;
mod func;

use builder::AsmBuilder;
use func::FunctionInfo;
use koopa::ir::entities::ValueData;
use koopa::ir::{BasicBlock, Function, FunctionData, Program, Type, Value, ValueKind};
use std::collections::HashMap;
use std::fs::File;
use std::io::{Result, Write};

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

/// A global/local value.
enum AsmValue<'i> {
  Global(&'i str),
  Local(usize),
  Temp,
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
    // get entry basic block
    let entry_bb = match self.layout().entry_bb() {
      Some(bb) => bb,
      // skip declarations
      None => return Ok(()),
    };
    // create function information
    let mut is_leaf = true;
    let mut max_arg_num = 0;
    for value in self.dfg().values().values() {
      match value.kind() {
        ValueKind::Call(call) => {
          is_leaf = false;
          if call.args().len() > max_arg_num {
            max_arg_num = call.args().len();
          }
        }
        _ => {}
      }
    }
    let mut func = FunctionInfo::new(is_leaf, max_arg_num);
    // generate allocations in entry basic block
    for &inst in self.layout().bbs()[&entry_bb].insts().keys() {
      let data = self.dfg().value(inst);
      match data.kind() {
        ValueKind::Alloc(_) => func.new_alloc(inst, data.ty()),
        _ => {}
      }
    }
    // generate basic block names
    for (&bb, data) in self.dfg().bbs() {
      // basic block parameters are not supported
      assert!(data.params().is_empty());
      func.log_bb_name(bb, data.name());
    }
    // generate prologue
    AsmBuilder::new(f, "t0").prologue(self.name(), &func)?;
    // update function information
    info.cur_func = Some(func);
    // generate instructions in basic blocks
    for (bb, node) in self.layout().bbs() {
      let name = bb.generate(f, info)?;
      writeln!(f, "{name}:")?;
      for &inst in node.insts().keys() {
        self.dfg().value(inst).generate(f, info)?;
      }
    }
    // generate epilogue
    AsmBuilder::new(f, "t0").epilogue(&info.cur_func.take().unwrap())
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for BasicBlock {
  type Out = &'i str;

  fn generate(&self, _: &mut File, info: &'i mut ProgramInfo) -> Result<Self::Out> {
    Ok(cur_func!(info).bb_name(*self))
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
      Ok(match cur_func!(info).size_of(*self) {
        Some(slot) => AsmValue::Local(slot),
        None => AsmValue::Temp,
      })
    }
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for ValueData {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    todo!()
  }
}
