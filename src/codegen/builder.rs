use super::func::FunctionInfo;
use std::fs::File;
use std::io::{Result, Write};

/// Assembly builder.
pub struct AsmBuilder<'f> {
  f: &'f mut File,
  temp: &'static str,
}

impl<'f> AsmBuilder<'f> {
  /// Creates a new assembly builder.
  pub fn new(f: &'f mut File, temp: &'static str) -> Self {
    Self { f, temp }
  }

  pub fn li(&mut self, dest: &str, imm: i32) -> Result<()> {
    writeln!(self.f, "  li {dest}, {imm}")
  }

  pub fn la(&mut self, dest: &str, symbol: &str) -> Result<()> {
    writeln!(self.f, "  la {dest}, {symbol}")
  }

  pub fn mv(&mut self, dest: &str, src: &str) -> Result<()> {
    if dest != src {
      writeln!(self.f, "  mv {dest}, {src}")
    } else {
      Ok(())
    }
  }

  pub fn addi(&mut self, dest: &str, opr: &str, offset: i32) -> Result<()> {
    if offset >= -2048 && offset <= 2047 {
      writeln!(self.f, "  addi {dest}, {opr}, {offset}")
    } else {
      self.li(self.temp, offset)?;
      writeln!(self.f, "  add {dest}, {opr}, {}", self.temp)
    }
  }

  pub fn sw(&mut self, src: &str, addr: &str, offset: i32) -> Result<()> {
    if offset >= -2048 && offset <= 2047 {
      writeln!(self.f, "  sw {src}, {offset}({addr})")
    } else {
      self.addi(self.temp, addr, offset)?;
      writeln!(self.f, "  sw {src}, 0({})", self.temp)
    }
  }

  pub fn lw(&mut self, dest: &str, addr: &str, offset: i32) -> Result<()> {
    if offset >= -2048 && offset <= 2047 {
      writeln!(self.f, "  lw {dest}, {offset}({addr})")
    } else {
      self.addi(self.temp, addr, offset)?;
      writeln!(self.f, "  lw {dest}, 0({})", self.temp)
    }
  }

  pub fn prologue(&mut self, func_name: &str, info: &FunctionInfo) -> Result<()> {
    // declaration
    writeln!(self.f, "  .text")?;
    writeln!(self.f, "  .globl {}", &func_name[1..])?;
    writeln!(self.f, "{}:", &func_name[1..])?;
    // prologue
    let offset = info.sp_offset() as i32;
    if offset != 0 {
      self.addi("sp", "sp", -offset)?;
      if !info.is_leaf() {
        self.sw("ra", "sp", offset - 4)?;
      }
    }
    Ok(())
  }

  pub fn epilogue(&mut self, info: &FunctionInfo) -> Result<()> {
    let offset = info.sp_offset() as i32;
    if offset != 0 {
      if !info.is_leaf() {
        self.lw("ra", "sp", offset - 4)?;
      }
      self.addi("sp", "sp", offset)?;
    }
    writeln!(self.f, "  ret")
  }
}
