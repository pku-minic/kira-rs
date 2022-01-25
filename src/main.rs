mod ast;
mod codegen;
mod irgen;

use koopa::back::KoopaGenerator;
use lalrpop_util::lalrpop_mod;
use std::env::args;
use std::fs::read_to_string;
use std::process::exit;
use std::{fmt, io};

lalrpop_mod! {
  #[allow(clippy::all)]
  sysy
}

fn main() {
  if let Err(err) = try_main() {
    eprintln!("{}", err);
    exit(-1);
  }
}

fn try_main() -> Result<(), Error> {
  // parse command line arguments
  let CommandLineArgs {
    mode,
    input,
    output,
  } = CommandLineArgs::parse()?;
  // parse input file
  let input = read_to_string(input).map_err(Error::File)?;
  let comp_unit = sysy::CompUnitParser::new()
    .parse(&input)
    .map_err(|_| Error::Parse)?;
  // generate IR
  let program = irgen::generate_program(&comp_unit).map_err(Error::Generate)?;
  if matches!(mode, Mode::Koopa) {
    return KoopaGenerator::from_path(output)
      .map_err(Error::File)?
      .generate_on(&program)
      .map_err(Error::Io);
  }
  // generate RISC-V assembly
  codegen::generate_asm(&program, &output).map_err(Error::Io)
}

/// Error returned by `main` procedure.
enum Error {
  InvalidArgs,
  File(io::Error),
  Parse,
  Generate(irgen::Error),
  Io(io::Error),
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::InvalidArgs => write!(
        f,
        r#"Usage: kira MODE INPUT -o OUTPUT

Options:
  MODE:   can be `-koopa`, `-riscv` or `-perf`
  INPUT:  the input SysY source file
  OUTPUT: the output file"#
      ),
      Self::File(err) => write!(f, "invalid input SysY file: {}", err),
      Self::Parse => write!(f, "error occurred while parsing"),
      Self::Generate(err) => write!(f, "{}", err),
      Self::Io(err) => write!(f, "I/O error: {}", err),
    }
  }
}

/// Command line arguments.
struct CommandLineArgs {
  mode: Mode,
  input: String,
  output: String,
}

impl CommandLineArgs {
  /// Parses the command line arguments, returns `Error` if error occurred.
  fn parse() -> Result<Self, Error> {
    let mut args = args();
    args.next();
    match (args.next(), args.next(), args.next(), args.next()) {
      (Some(m), Some(input), Some(o), Some(output)) if o == "-o" => {
        let mode = match m.as_str() {
          "-koopa" => Mode::Koopa,
          "-riscv" => Mode::Riscv,
          "-perf" => Mode::Perf,
          _ => return Err(Error::InvalidArgs),
        };
        Ok(Self {
          mode,
          input,
          output,
        })
      }
      _ => Err(Error::InvalidArgs),
    }
  }
}

/// Compile mode.
enum Mode {
  /// Compile SysY to Koopa IR.
  Koopa,
  /// Compile SysY to RISC-V assembly.
  Riscv,
  /// Compile SysY to optimized RISC-V assembly.
  Perf,
}
