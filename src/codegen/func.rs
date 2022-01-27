use koopa::ir::entities::ValueData;
use koopa::ir::{BasicBlock, Function, TypeKind, ValueKind};
use std::cell::Cell;
use std::collections::HashMap;

/// Function information.
pub struct FunctionInfo {
  func: Function,
  /// Maximum argument number of call instructions in the function.
  /// `None` if the current function is a leaf function.
  max_arg_num: Option<usize>,
  alloc_size: usize,
  allocs: HashMap<*const ValueData, Slot>,
  bbs: HashMap<BasicBlock, String>,
  sp_offset: Cell<Option<usize>>,
}

impl FunctionInfo {
  thread_local! {
    static NEXT_TEMP_LABEL_ID: Cell<usize> = Cell::new(0);
  }

  /// Creates a new function information.
  pub fn new(func: Function) -> Self {
    Self {
      func,
      max_arg_num: None,
      alloc_size: 0,
      allocs: HashMap::new(),
      bbs: HashMap::new(),
      sp_offset: Cell::new(None),
    }
  }

  /// Returns the current function.
  pub fn func(&self) -> Function {
    self.func
  }

  /// Logs argument number.
  pub fn log_arg_num(&mut self, arg_num: usize) {
    if self.max_arg_num.is_none() || arg_num > self.max_arg_num.unwrap() {
      self.max_arg_num = Some(arg_num);
    }
  }

  /// Returns `true` if the current function is a leaf function.
  pub fn is_leaf(&self) -> bool {
    self.max_arg_num.is_none()
  }

  /// Allocates a new stack slot for the given value data.
  pub fn alloc_slot(&mut self, value: &ValueData) {
    match value.kind() {
      ValueKind::Alloc(_) => {
        self.allocs.insert(value, Slot::new(self.alloc_size, false));
        self.alloc_size += match value.ty().kind() {
          TypeKind::Pointer(base) => base.size(),
          _ => unreachable!(),
        };
      }
      _ => {
        let is_ptr = matches!(value.ty().kind(), TypeKind::Pointer(_));
        let slot = Slot::new(self.alloc_size, is_ptr);
        self.allocs.insert(value, slot);
        self.alloc_size += value.ty().size();
      }
    };
  }

  /// Returns the slot offset (relative to `sp`) of the given value data.
  pub fn slot_offset(&self, value: &ValueData) -> Slot {
    let offset = *self.allocs.get(&(value as *const ValueData)).unwrap();
    if self.is_leaf() {
      offset.map(|o| self.sp_offset() - self.alloc_size + o)
    } else {
      offset.map(|o| self.sp_offset() - 4 - self.alloc_size + o)
    }
  }

  /// Logs basic block name.
  pub fn log_bb_name(&mut self, bb: BasicBlock, name: &Option<String>) {
    let id = Self::NEXT_TEMP_LABEL_ID.with(|id| id.replace(id.get() + 1));
    let name = match name.as_ref() {
      Some(name) => format!(".L{}_{}", &name[1..], id),
      None => format!(".L{}", id),
    };
    self.bbs.insert(bb, name);
  }

  /// Returns a reference to the name of the given basic block.
  pub fn bb_name(&self, bb: BasicBlock) -> &str {
    self.bbs.get(&bb).as_ref().unwrap()
  }

  /// Returns the stack pointer offset.
  pub fn sp_offset(&self) -> usize {
    if let Some(sp_offset) = self.sp_offset.get() {
      sp_offset
    } else {
      // slot for storing return address
      let ra = if self.is_leaf() { 0 } else { 1 };
      // slot for storing arguments
      let args = match self.max_arg_num {
        Some(num) if num > 8 => num - 8,
        _ => 0,
      };
      // the final offset
      let offset = ra + self.alloc_size + args;
      // align to 16 bytes
      let sp_offset = (offset + 15) / 16 * 16;
      self.sp_offset.set(Some(sp_offset));
      sp_offset
    }
  }
}

/// A stack slot.
#[derive(Clone, Copy)]
pub struct Slot {
  pub offset: usize,
  /// `true` if the slot stores an pointer but not an allocation.
  pub is_ptr: bool,
}

impl Slot {
  /// Creates a new stack slot.
  fn new(offset: usize, is_ptr: bool) -> Self {
    Self { offset, is_ptr }
  }

  /// Maps the offset by applying the given function.
  fn map<F>(self, f: F) -> Self
  where
    F: FnOnce(usize) -> usize,
  {
    Self {
      offset: f(self.offset),
      is_ptr: self.is_ptr,
    }
  }
}
