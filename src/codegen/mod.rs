mod builder;
mod func;

use builder::AsmBuilder;
use func::FunctionInfo;
use koopa::ir::entities::ValueData;
use koopa::ir::values::*;
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
  Const(i32),
}

/// Trait for generating RISC-V assembly.
trait GenerateAsm<'p, 'i> {
  type Out;

  fn generate(&self, f: &mut File, info: &'i mut ProgramInfo<'p>) -> Result<Self::Out>;
}

impl<'p, 'i> GenerateAsm<'p, 'i> for Program {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    for &value in self.inst_layout() {
      self.borrow_value(value).generate(f, info)?;
    }
    for &func in self.func_layout() {
      info.cur_func = Some(FunctionInfo::new(func));
      self.func(func).generate(f, info)?;
    }
    Ok(())
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for Function {
  type Out = &'p str;

  fn generate(&self, _: &mut File, info: &mut ProgramInfo<'p>) -> Result<Self::Out> {
    Ok(info.program.func(*self).name())
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for FunctionData {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    // skip declarations
    if self.layout().entry_bb().is_none() {
      return Ok(());
    }
    // allocation stack slots and log argument number
    let func = cur_func_mut!(info);
    for value in self.dfg().values().values() {
      if value.kind().is_local_inst() {
        // allocate stack slot
        if !value.used_by().is_empty() && !value.ty().is_unit() {
          func.alloc_slot(value);
        }
        // log argument number
        if let ValueKind::Call(call) = value.kind() {
          func.log_arg_num(call.args().len());
        }
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
      let func = cur_func!(info);
      let value = info.program.func(func.func()).dfg().value(*self);
      Ok(match value.kind() {
        ValueKind::Integer(i) => AsmValue::Const(i.value()),
        _ => AsmValue::Local(func.slot_offset(value)),
      })
    }
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for ValueData {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    match self.kind() {
      ValueKind::GlobalAlloc(v) => v.generate(f, info),
      ValueKind::Load(v) => v.generate(f, info),
      ValueKind::Store(v) => v.generate(f, info),
      ValueKind::GetPtr(v) => v.generate(f, info),
      ValueKind::GetElemPtr(v) => v.generate(f, info),
      ValueKind::Binary(v) => v.generate(f, info),
      ValueKind::Branch(v) => v.generate(f, info),
      ValueKind::Jump(v) => v.generate(f, info),
      ValueKind::Call(v) => v.generate(f, info),
      ValueKind::Return(v) => v.generate(f, info),
      _ => Ok(()),
    }
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for GlobalAlloc {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    todo!()
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for Load {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    todo!()
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for Store {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    todo!()
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for GetPtr {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    todo!()
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for GetElemPtr {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    todo!()
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for Binary {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    todo!()
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for Branch {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    todo!()
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for Jump {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    todo!()
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for Call {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    todo!()
  }
}

impl<'p, 'i> GenerateAsm<'p, 'i> for Return {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    todo!()
  }
}
