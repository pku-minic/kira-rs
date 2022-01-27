use super::builder::AsmBuilder;
use std::fs::File;
use std::io::Result;

/// A global/local value.
pub enum AsmValue<'i> {
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
pub(crate) use asm_value;

impl<'i> AsmValue<'i> {
  /// Writes the assembly value to the given register.
  pub fn write_to(&self, f: &mut File, reg: &'static str) -> Result<()> {
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
  pub fn write_addr_to(&self, f: &mut File, reg: &'static str) -> Result<()> {
    let mut builder = AsmBuilder::new(f, reg);
    match self {
      Self::Global(symbol) => builder.la(reg, symbol),
      Self::Local(offset) => builder.addi(reg, "sp", *offset as i32),
      _ => unreachable!(),
    }
  }

  /// Writes the assembly value (argument) to the given register.
  pub fn write_arg_to(&self, f: &mut File, reg: &'static str, sp_offset: usize) -> Result<()> {
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
  pub fn read_from(&self, f: &mut File, reg: &'static str, temp: &'static str) -> Result<()> {
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
pub enum LocalValue {
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
