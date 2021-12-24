use crate::ExitError;
use alloc::vec::Vec;
// use amzn_smt_ir::Term;
// use primitive_types::H256;

pub trait StackItem = Copy;

// #[derive(Clone, Debug)]
// pub enum SymStackItem {
// 	Concrete(H256),
// 	Symbolic(Term)
// }

/// EVM stack.
#[derive(Clone, Debug)]
pub struct Stack<T: StackItem> {
	data: Vec<T>,
	limit: usize,
}

impl<T: StackItem> Stack<T> {
	/// Create a new stack with given limit.
	pub fn new(limit: usize) -> Self {
		Self {
			data: Vec::new(),
			limit,
		}
	}

	#[inline]
	/// Stack limit.
	pub fn limit(&self) -> usize {
		self.limit
	}

	#[inline]
	/// Stack length.
	pub fn len(&self) -> usize {
		self.data.len()
	}

	#[inline]
	/// Whether the stack is empty.
	pub fn is_empty(&self) -> bool {
		self.data.is_empty()
	}

	#[inline]
	/// Pop a value from the stack. If the stack is already empty, returns the
	/// `StackUnderflow` error.
	pub fn pop(&mut self) -> Result<T, ExitError> {
		self.data.pop().ok_or(ExitError::StackUnderflow)
	}

	#[inline]
	/// Push a new value into the stack. If it will exceed the stack limit,
	/// returns `StackOverflow` error and leaves the stack unchanged.
	pub fn push(&mut self, value: T) -> Result<(), ExitError> {
		if self.data.len() + 1 > self.limit {
			return Err(ExitError::StackOverflow);
		}
		self.data.push(value);
		Ok(())
	}

	#[inline]
	/// Peek a value at given index for the stack, where the top of
	/// the stack is at index `0`. If the index is too large,
	/// `StackError::Underflow` is returned.
	pub fn peek(&self, no_from_top: usize) -> Result<T, ExitError> {
		if self.data.len() > no_from_top {
			Ok(self.data[self.data.len() - no_from_top - 1])
		} else {
			Err(ExitError::StackUnderflow)
		}
	}

	#[inline]
	/// Set a value at given index for the stack, where the top of the
	/// stack is at index `0`. If the index is too large,
	/// `StackError::Underflow` is returned.
	pub fn set(&mut self, no_from_top: usize, val: T) -> Result<(), ExitError> {
		if self.data.len() > no_from_top {
			let len = self.data.len();
			self.data[len - no_from_top - 1] = val;
			Ok(())
		} else {
			Err(ExitError::StackUnderflow)
		}
	}
}
