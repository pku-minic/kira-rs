use koopa::ir::{BasicBlock, Type, Value};
use std::collections::HashMap;

/// Function information.
pub struct FunctionInfo {
  is_leaf: bool,
  max_arg_num: usize,
  alloc_size: usize,
  allocs: HashMap<Value, usize>,
  bbs: HashMap<BasicBlock, String>,
}

impl FunctionInfo {
  /// Creates a new function information.
  pub fn new(is_leaf: bool, max_arg_num: usize) -> Self {
    Self {
      is_leaf,
      max_arg_num,
      alloc_size: 0,
      allocs: HashMap::new(),
      bbs: HashMap::new(),
    }
  }

  /// Returns `true` if the current function is a leaf function.
  pub fn is_leaf(&self) -> bool {
    self.is_leaf
  }

  /// Returns the maximum argument number of call instructions in function.
  pub fn max_arg_num(&self) -> usize {
    self.max_arg_num
  }

  /// Creates a new stack slot allocation.
  pub fn new_alloc(&mut self, alloc: Value, ty: &Type) {
    self.allocs.insert(alloc, self.alloc_size);
    self.alloc_size += ty.size();
  }

  /// Returns the size of the given allocation.
  pub fn size_of(&self, alloc: Value) -> Option<usize> {
    self.allocs.get(&alloc).copied()
  }

  /// Returns a reference to the name of the given basic block.
  pub fn bb_name(&self, bb: BasicBlock) -> &str {
    self.bbs.get(&bb).as_ref().unwrap()
  }

  /// Returns the stack pointer offset.
  pub fn sp_offset(&self) -> usize {
    // slot for storing return address
    let ra = if self.is_leaf { 0 } else { 1 };
    // slot for storing arguments and temporary arguments
    let (args, temp_args) = if self.max_arg_num > 8 {
      (self.max_arg_num - 8, 8)
    } else {
      (0, self.max_arg_num)
    };
    // the final offset
    let offset = ra + args + temp_args + self.alloc_size;
    // align to 16 bytes
    (offset + 15) / 16 * 16
  }
}
