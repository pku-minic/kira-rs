mod builder;
mod func;

use builder::AsmBuilder;
use func::FunctionInfo;
use koopa::ir::entities::ValueData;
use koopa::ir::values::*;
use koopa::ir::{BasicBlock, Function, FunctionData, Program, Type, TypeKind, Value, ValueKind};
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
}

/// A global/local value.
enum AsmValue<'i> {
  Global(&'i str),
  Local(usize),
  Const(i32),
  Arg(usize),
}

/// Returns the assembly value of the given value data.
macro_rules! asm_value {
  ($info:expr, $v:expr) => {
    AsmValue::Local(cur_func!($info).slot_offset($v))
  };
}

impl<'i> AsmValue<'i> {
  /// Writes the assembly value to the given register.
  fn write_to(&self, f: &mut File, reg: &'static str) -> Result<()> {
    let mut builder = AsmBuilder::new(f, reg);
    match self {
      Self::Global(symbol) => {
        builder.la(reg, symbol)?;
        builder.lw(reg, reg, 0)
      }
      Self::Local(offset) => builder.lw(reg, "sp", *offset as i32),
      Self::Const(num) => builder.li(reg, *num),
      _ => unreachable!(),
    }
  }

  /// Writes the address of assembly value to the give register.
  fn write_addr_to(&self, f: &mut File, reg: &'static str) -> Result<()> {
    let mut builder = AsmBuilder::new(f, reg);
    match self {
      Self::Global(symbol) => builder.la(reg, symbol),
      Self::Local(offset) => builder.addi(reg, "sp", *offset as i32),
      _ => unreachable!(),
    }
  }

  /// Writes the assembly value (argument) to the given register.
  fn write_arg_to(&self, f: &mut File, reg: &'static str, sp_offset: usize) -> Result<()> {
    let mut builder = AsmBuilder::new(f, reg);
    match self {
      Self::Arg(index) => {
        if *index < 8 {
          builder.mv(reg, &format!("a{}", *index))
        } else {
          builder.lw(reg, "sp", (sp_offset + (*index - 8) * 4) as i32)
        }
      }
      _ => unreachable!(),
    }
  }

  /// Reads the value of the given register to the assembly value.
  fn read_from(&self, f: &mut File, reg: &'static str, temp: &'static str) -> Result<()> {
    let mut builder = AsmBuilder::new(f, temp);
    match self {
      Self::Global(symbol) => {
        builder.la(temp, symbol)?;
        builder.sw(reg, temp, 0)
      }
      Self::Local(offset) => builder.sw(reg, "sp", *offset as i32),
      Self::Const(_) => unreachable!(),
      Self::Arg(index) => {
        if *index < 8 {
          builder.mv(&format!("a{}", *index), reg)
        } else {
          builder.sw(reg, "sp", ((*index - 8) * 4) as i32)
        }
      }
    }
  }
}

impl<'i> From<LocalValue> for AsmValue<'i> {
  fn from(v: LocalValue) -> Self {
    match v {
      LocalValue::Local(offset) => Self::Local(offset),
      LocalValue::Const(num) => Self::Const(num),
    }
  }
}

/// A local value (simplified version of assembly value).
enum LocalValue {
  Local(usize),
  Const(i32),
}

impl<'i> From<AsmValue<'i>> for LocalValue {
  fn from(value: AsmValue) -> Self {
    match value {
      AsmValue::Local(offset) => Self::Local(offset),
      AsmValue::Const(num) => Self::Const(num),
      _ => unreachable!(),
    }
  }
}

/// Trait for generating RISC-V assembly.
trait GenerateToAsm<'p, 'i> {
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
      info.values.insert(value, name.into());
      writeln!(f, "  .data")?;
      writeln!(f, "  .globl {name}")?;
      writeln!(f, "{name}:")?;
      data.generate(f, info)?;
      writeln!(f, "")?;
    }
    // generate functions
    for &func in self.func_layout() {
      info.cur_func = Some(FunctionInfo::new(func));
      self.func(func).generate(f, info)?;
      writeln!(f, "")?;
    }
    Ok(())
  }
}

impl<'p, 'i> GenerateToAsm<'p, 'i> for Function {
  type Out = &'p str;

  fn generate(&self, _: &mut File, info: &mut ProgramInfo<'p>) -> Result<Self::Out> {
    Ok(info.program.func(*self).name())
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
      Ok(AsmValue::Global(info.values.get(self).as_ref().unwrap()))
    } else {
      let func = cur_func!(info);
      let value = info.program.func(func.func()).dfg().value(*self);
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
      info.program.borrow_value(elem).generate(f, info)?;
    }
    Ok(())
  }
}

impl<'p, 'i> GenerateToAsm<'p, 'i> for GlobalAlloc {
  type Out = ();

  fn generate(&self, f: &mut File, info: &mut ProgramInfo) -> Result<Self::Out> {
    info.program.borrow_value(self.init()).generate(f, info)
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
