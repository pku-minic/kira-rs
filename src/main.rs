mod ast;

use lalrpop_util::lalrpop_mod;
use std::env::args;
use std::fs::read_to_string;
use std::process::exit;
use std::{fmt, io};

lalrpop_mod!(sysy);

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
  todo!()
}

/// Error returned by `main` procedure.
enum Error {
  InvalidArgs,
  File(io::Error),
  Parse,
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Error::InvalidArgs => write!(f, ""),
      Error::File(err) => write!(f, "invalid input SysY file: {}", err),
      Error::Parse => write!(f, "error occurred while parsing"),
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
