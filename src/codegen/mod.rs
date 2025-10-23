mod builder;
mod func;
mod generate;
mod info;
mod values;

use generate::GenerateToAsm;
use info::ProgramInfo;
use koopa::ir::{Program, Type};
use std::fs::File;
use std::io::Result;

/// Generates the given Koopa IR program to RISC-V assembly.
pub fn generate_asm(program: &Program, path: &str) -> Result<()> {
  Type::set_ptr_size(4);
  program.generate(&mut File::create(path)?, &mut ProgramInfo::new(program))
}
