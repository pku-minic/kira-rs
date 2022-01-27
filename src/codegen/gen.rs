use super::builder::AsmBuilder;
use super::func::FunctionInfo;
use super::info::{cur_func, cur_func_mut, ProgramInfo};
use super::values::{asm_value, AsmValue, LocalValue};
use koopa::ir::entities::ValueData;
use koopa::ir::values::*;
use koopa::ir::{BasicBlock, Function, FunctionData, Program, TypeKind, Value, ValueKind};
use std::fs::File;
use std::io::{Result, Write};

/// Trait for generating RISC-V assembly.
pub trait GenerateToAsm<'p, 'i> {
  type Out;

  fn generate(&self, f: &mut File, info: &'i mut ProgramInfo<'p>) -> Result<Self::Out>;
}

/// Trait for generating RISC-V assembly (for values).
trait GenerateValueToAsm<'p, 'i> {
  type Out;

  fn generate(
    &self,
    f: &mut File,
    info: &'i mut ProgramInfo<'p>,
    v: &ValueData,
  ) -> Result<Self::Out>;
}

impl<'p, 'i> GenerateToAsm<'p, 'i> for Program {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    // generate global allocations
    for &value in self.inst_layout() {
      let data = self.borrow_value(value);
      let name = &data.name().as_ref().unwrap()[1..];
      info.insert_value(value, name.into());
      writeln!(f, "  .data")?;
      writeln!(f, "  .globl {name}")?;
      writeln!(f, "{name}:")?;
      data.generate(f, info)?;
      writeln!(f, "")?;
    }
    // generate functions
    for &func in self.func_layout() {
      info.set_cur_func(FunctionInfo::new(func));
      self.func(func).generate(f, info)?;
      writeln!(f, "")?;
    }
    Ok(())
  }
}

impl<'p, 'i> GenerateToAsm<'p, 'i> for Function {
  type Out = &'p str;

  fn generate(&self, _: &mut File, info: &mut ProgramInfo<'p>) -> Result<Self::Out> {
    Ok(info.program().func(*self).name())
  }
}

impl<'p, 'i> GenerateToAsm<'p, 'i> for FunctionData {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    // skip declarations
    if self.layout().entry_bb().is_none() {
      return Ok(());
    }
    // allocation stack slots and log argument number
    let func = cur_func_mut!(info);
    for value in self.dfg().values().values() {
      // allocate stack slot
      if value.kind().is_local_inst() && !value.used_by().is_empty() {
        func.alloc_slot(value);
      }
      // log argument number
      if let ValueKind::Call(call) = value.kind() {
        func.log_arg_num(call.args().len());
      }
    }
    // generate basic block names
    for (&bb, data) in self.dfg().bbs() {
      // basic block parameters are not supported
      assert!(data.params().is_empty());
      func.log_bb_name(bb, data.name());
    }
    // generate prologue
    AsmBuilder::new(f, "t0").prologue(self.name(), func)?;
    // generate instructions in basic blocks
    for (bb, node) in self.layout().bbs() {
      let name = bb.generate(f, info)?;
      writeln!(f, "{name}:")?;
      for &inst in node.insts().keys() {
        self.dfg().value(inst).generate(f, info)?;
      }
    }
    Ok(())
  }
}

impl<'p, 'i> GenerateToAsm<'p, 'i> for BasicBlock {
  type Out = &'i str;

  fn generate(&self, _: &mut File, info: &'i mut ProgramInfo) -> Result<Self::Out> {
    Ok(cur_func!(info).bb_name(*self))
  }
}

impl<'p, 'i> GenerateToAsm<'p, 'i> for Value {
  type Out = AsmValue<'i>;

  fn generate(&self, _: &mut File, info: &'i mut ProgramInfo) -> Result<Self::Out> {
    if self.is_global() {
      Ok(AsmValue::Global(info.value(*self)))
    } else {
      let func = cur_func!(info);
      let value = info.program().func(func.func()).dfg().value(*self);
      Ok(match value.kind() {
        ValueKind::Integer(i) => AsmValue::Const(i.value()),
        ValueKind::FuncArgRef(i) => AsmValue::Arg(i.index()),
        _ => AsmValue::Local(func.slot_offset(value)),
      })
    }
  }
}

impl<'p, 'i> GenerateToAsm<'p, 'i> for ValueData {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    match self.kind() {
      ValueKind::Integer(v) => v.generate(f, info),
      ValueKind::ZeroInit(v) => v.generate(f, info, self),
      ValueKind::Aggregate(v) => v.generate(f, info),
      ValueKind::GlobalAlloc(v) => v.generate(f, info),
      ValueKind::Load(v) => v.generate(f, info, self),
      ValueKind::Store(v) => v.generate(f, info),
      ValueKind::GetPtr(v) => v.generate(f, info, self),
      ValueKind::GetElemPtr(v) => v.generate(f, info, self),
      ValueKind::Binary(v) => v.generate(f, info, self),
      ValueKind::Branch(v) => v.generate(f, info),
      ValueKind::Jump(v) => v.generate(f, info),
      ValueKind::Call(v) => v.generate(f, info, self),
      ValueKind::Return(v) => v.generate(f, info),
      _ => Ok(()),
    }
  }
}

impl<'p, 'i> GenerateToAsm<'p, 'i> for Integer {
  type Out = ();

  fn generate(&self, f: &mut File, _: &mut ProgramInfo) -> Result<Self::Out> {
    writeln!(f, "  .word {}", self.value())
  }
}

impl<'p, 'i> GenerateValueToAsm<'p, 'i> for ZeroInit {
  type Out = ();

  fn generate(&self, f: &mut File, _: &mut ProgramInfo, v: &ValueData) -> Result<Self::Out> {
    writeln!(f, "  .zero {}", v.ty().size())
  }
}

impl<'p, 'i> GenerateToAsm<'p, 'i> for Aggregate {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    for &elem in self.elems() {
      info.program().borrow_value(elem).generate(f, info)?;
    }
    Ok(())
  }
}

impl<'p, 'i> GenerateToAsm<'p, 'i> for GlobalAlloc {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    info.program().borrow_value(self.init()).generate(f, info)
  }
}

impl<'p, 'i> GenerateValueToAsm<'p, 'i> for Load {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo, v: &ValueData) -> Result<Self::Out> {
    self.src().generate(f, info)?.write_to(f, "t0")?;
    asm_value!(info, v).read_from(f, "t0", "t1")
  }
}

impl<'p, 'i> GenerateToAsm<'p, 'i> for Store {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    let sp_offset = cur_func!(info).sp_offset();
    let value = self.value().generate(f, info)?;
    if matches!(value, AsmValue::Arg(_)) {
      value.write_arg_to(f, "t0", sp_offset)?;
    } else {
      value.write_to(f, "t0")?;
    }
    self.dest().generate(f, info)?.read_from(f, "t0", "t1")
  }
}

impl<'p, 'i> GenerateValueToAsm<'p, 'i> for GetPtr {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo, v: &ValueData) -> Result<Self::Out> {
    self.src().generate(f, info)?.write_addr_to(f, "t0")?;
    self.index().generate(f, info)?.write_to(f, "t1")?;
    let size = match v.ty().kind() {
      TypeKind::Pointer(base) => base.size(),
      _ => unreachable!(),
    };
    let mut builder = AsmBuilder::new(f, "t2");
    builder.muli("t1", "t1", size as i32)?;
    builder.op2("add", "t0", "t0", "t1")?;
    asm_value!(info, v).read_from(f, "t0", "t1")
  }
}

impl<'p, 'i> GenerateValueToAsm<'p, 'i> for GetElemPtr {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo, v: &ValueData) -> Result<Self::Out> {
    self.src().generate(f, info)?.write_addr_to(f, "t0")?;
    self.index().generate(f, info)?.write_to(f, "t1")?;
    let size = match v.ty().kind() {
      TypeKind::Pointer(base) => match base.kind() {
        TypeKind::Array(base, _) => base.size(),
        _ => unreachable!(),
      },
      _ => unreachable!(),
    };
    let mut builder = AsmBuilder::new(f, "t2");
    builder.muli("t1", "t1", size as i32)?;
    builder.op2("add", "t0", "t0", "t1")?;
    asm_value!(info, v).read_from(f, "t0", "t1")
  }
}

impl<'p, 'i> GenerateValueToAsm<'p, 'i> for Binary {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo, v: &ValueData) -> Result<Self::Out> {
    self.lhs().generate(f, info)?.write_to(f, "t0")?;
    self.rhs().generate(f, info)?.write_to(f, "t1")?;
    let mut builder = AsmBuilder::new(f, "t2");
    match self.op() {
      BinaryOp::NotEq => {
        builder.op2("xor", "t0", "t0", "t1")?;
        builder.op1("snez", "t0", "t0")?;
      }
      BinaryOp::Eq => {
        builder.op2("xor", "t0", "t0", "t1")?;
        builder.op1("seqz", "t0", "t0")?;
      }
      BinaryOp::Gt => builder.op2("sgt", "t0", "t0", "t1")?,
      BinaryOp::Lt => builder.op2("slt", "t0", "t0", "t1")?,
      BinaryOp::Ge => {
        builder.op2("slt", "t0", "t0", "t1")?;
        builder.op1("seqz", "t0", "t0")?;
      }
      BinaryOp::Le => {
        builder.op2("sgt", "t0", "t0", "t1")?;
        builder.op1("seqz", "t0", "t0")?;
      }
      BinaryOp::Add => builder.op2("add", "t0", "t0", "t1")?,
      BinaryOp::Sub => builder.op2("sub", "t0", "t0", "t1")?,
      BinaryOp::Mul => builder.op2("mul", "t0", "t0", "t1")?,
      BinaryOp::Div => builder.op2("div", "t0", "t0", "t1")?,
      BinaryOp::Mod => builder.op2("rem", "t0", "t0", "t1")?,
      BinaryOp::And => builder.op2("and", "t0", "t0", "t1")?,
      BinaryOp::Or => builder.op2("or", "t0", "t0", "t1")?,
      BinaryOp::Xor => builder.op2("xor", "t0", "t0", "t1")?,
      BinaryOp::Shl => builder.op2("sll", "t0", "t0", "t1")?,
      BinaryOp::Shr => builder.op2("srl", "t0", "t0", "t1")?,
      BinaryOp::Sar => builder.op2("sra", "t0", "t0", "t1")?,
    }
    asm_value!(info, v).read_from(f, "t0", "t1")
  }
}

impl<'p, 'i> GenerateToAsm<'p, 'i> for Branch {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    self.cond().generate(f, info)?.write_to(f, "t0")?;
    let tlabel = self.true_bb().generate(f, info)?;
    AsmBuilder::new(f, "t1").bnez("t0", tlabel)?;
    let flabel = self.false_bb().generate(f, info)?;
    AsmBuilder::new(f, "t1").j(flabel)
  }
}

impl<'p, 'i> GenerateToAsm<'p, 'i> for Jump {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    let label = self.target().generate(f, info)?;
    AsmBuilder::new(f, "t0").j(label)
  }
}

impl<'p, 'i> GenerateValueToAsm<'p, 'i> for Call {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo, v: &ValueData) -> Result<Self::Out> {
    let args = self
      .args()
      .iter()
      .map(|v| Ok(v.generate(f, info)?.into()))
      .collect::<Result<Vec<LocalValue>>>()?;
    for (i, arg) in args.into_iter().enumerate() {
      AsmValue::from(arg).write_to(f, "t0")?;
      AsmValue::Arg(i).read_from(f, "t0", "t1")?;
    }
    let callee = self.callee().generate(f, info)?;
    AsmBuilder::new(f, "t0").call(callee)?;
    asm_value!(info, v).read_from(f, "a0", "t0")
  }
}

impl<'p, 'i> GenerateToAsm<'p, 'i> for Return {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    if let Some(value) = self.value() {
      value.generate(f, info)?.write_to(f, "a0")?;
    }
    AsmBuilder::new(f, "t0").epilogue(cur_func!(info))
  }
}
