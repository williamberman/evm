//! Core layer for EVM.

#![deny(warnings)]
#![forbid(unsafe_code, unused_variables, unused_imports)]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;
extern crate core;

mod error;
mod eval;
mod memory;
mod opcode;
mod stack;
mod symbolic;
mod symbolic_calldata;
mod utils;
mod valids;

pub use crate::error::{Capture, ExitError, ExitFatal, ExitReason, ExitRevert, ExitSucceed, Trap};
pub use crate::memory::Memory;
pub use crate::opcode::Opcode;
pub use crate::stack::Stack;
pub use crate::valids::Valids;

use crate::eval::{Control};
use alloc::rc::Rc;
use alloc::vec::Vec;
use symbolic_calldata::SymbolicCalldata;
use core::ops::Range;
use eval::{DispatchTable, CONCRETE_TABLE, SYMBOLIC_TABLE};
use primitive_types::{H256, U256};
use stack::StackItem;

use symbolic::{SymWord};

pub type ConcreteMachine = Machine<H256, Vec<u8>>;
pub type SymbolicMachine = Machine<SymWord, SymbolicCalldata>;

/// Core execution layer for EVM.
pub struct Machine<IStackItem: StackItem, ICalldata> {
	/// Program data.
	data: ICalldata,
	/// Program code.
	code: Rc<Vec<u8>>,
	/// Program counter.
	position: Result<usize, ExitReason>,
	/// Return value.
	return_range: Range<U256>,
	/// Code validity maps.
	valids: Valids,
	/// Memory.
	memory: Memory,
	/// Stack.
	stack: Stack<IStackItem>,

	table: DispatchTable<IStackItem, ICalldata>,
}

impl ConcreteMachine {
	pub fn new_concrete(
		code: Rc<Vec<u8>>,
		data: Vec<u8>,
		stack_limit: usize,
		memory_limit: usize,
	) -> Self {
		Self::new(code, data, stack_limit, memory_limit, CONCRETE_TABLE)
	}
}

impl SymbolicMachine {
	pub fn new_symbolic(
		code: Rc<Vec<u8>>,
		data: SymbolicCalldata,
		stack_limit: usize,
		memory_limit: usize,
	) -> Self {
		Self::new(code, data, stack_limit, memory_limit, SYMBOLIC_TABLE)
	}
}

impl<IStackItem: StackItem, ICalldata> Machine<IStackItem, ICalldata> {
	/// Reference of machine stack.
	pub fn stack(&self) -> &Stack<IStackItem> {
		&self.stack
	}
	/// Mutable reference of machine stack.
	pub fn stack_mut(&mut self) -> &mut Stack<IStackItem> {
		&mut self.stack
	}
	/// Reference of machine memory.
	pub fn memory(&self) -> &Memory {
		&self.memory
	}
	/// Mutable reference of machine memory.
	pub fn memory_mut(&mut self) -> &mut Memory {
		&mut self.memory
	}
	/// Return a reference of the program counter.
	pub fn position(&self) -> &Result<usize, ExitReason> {
		&self.position
	}

	/// Create a new machine with given code and data.
	pub fn new(
		code: Rc<Vec<u8>>,
		data: ICalldata,
		stack_limit: usize,
		memory_limit: usize,
		table: DispatchTable<IStackItem, ICalldata>,
	) -> Self {
		let valids = Valids::new(&code[..]);

		Self {
			data,
			code,
			position: Ok(0),
			return_range: U256::zero()..U256::zero(),
			valids,
			memory: Memory::new(memory_limit),
			stack: Stack::new(stack_limit),
			table,
		}
	}

	/// Explicit exit of the machine. Further step will return error.
	pub fn exit(&mut self, reason: ExitReason) {
		self.position = Err(reason);
	}

	/// Inspect the machine's next opcode and current stack.
	pub fn inspect(&self) -> Option<(Opcode, &Stack<IStackItem>)> {
		let position = match self.position {
			Ok(position) => position,
			Err(_) => return None,
		};
		self.code.get(position).map(|v| (Opcode(*v), &self.stack))
	}

	/// Copy and get the return value of the machine, if any.
	pub fn return_value(&self) -> Vec<u8> {
		if self.return_range.start > U256::from(usize::MAX) {
			let mut ret = Vec::new();
			ret.resize(
				(self.return_range.end - self.return_range.start).as_usize(),
				0,
			);
			ret
		} else if self.return_range.end > U256::from(usize::MAX) {
			let mut ret = self.memory.get(
				self.return_range.start.as_usize(),
				usize::MAX - self.return_range.start.as_usize(),
			);
			while ret.len() < (self.return_range.end - self.return_range.start).as_usize() {
				ret.push(0);
			}
			ret
		} else {
			self.memory.get(
				self.return_range.start.as_usize(),
				(self.return_range.end - self.return_range.start).as_usize(),
			)
		}
	}

	/// Loop stepping the machine, until it stops.
	pub fn run(&mut self) -> Capture<ExitReason, Trap> {
		loop {
			match self.step() {
				Ok(()) => (),
				Err(res) => return res,
			}
		}
	}

	#[inline]
	/// Step the machine, executing one opcode. It then returns.
	pub fn step(&mut self) -> Result<(), Capture<ExitReason, Trap>> {
		let position = *self
			.position
			.as_ref()
			.map_err(|reason| Capture::Exit(reason.clone()))?;

		match self.code.get(position).map(|v| Opcode(*v)) {
			Some(opcode) => match self.table[opcode.as_usize()](self, opcode, position) {
				Control::Continue(p) => {
					self.position = Ok(position + p);
					Ok(())
				}
				Control::Exit(e) => {
					self.position = Err(e.clone());
					Err(Capture::Exit(e))
				}
				Control::Jump(p) => {
					self.position = Ok(p);
					Ok(())
				}
				Control::Trap(opcode) => {
					self.position = Ok(position + 1);
					Err(Capture::Trap(opcode))
				}
			},
			None => {
				self.position = Err(ExitSucceed::Stopped.into());
				Err(Capture::Exit(ExitSucceed::Stopped.into()))
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use crate::{symbolic::bv_constant_from_h256, Machine, Opcode, SymWord, SymbolicCalldata};
	use amzn_smt_ir::{logic::BvOp, Term};
	use primitive_types::H256;
	use smallvec::smallvec;
	use std::rc::Rc;

	#[test]
	fn test_concrete_add() {
		let a = H256::from_low_u64_be(255);
		let b = H256::from_low_u64_be(1);

		let code: Vec<u8> = vec![Opcode::ADD.0];

		let stack_limit = 1024;
		let memory_limit = 10000;

		let mut m = Machine::new_symbolic(
			Rc::new(code),
			SymbolicCalldata::default(),
			stack_limit,
			memory_limit,
		);

		m.stack_mut().push(SymWord::Concrete(a)).unwrap();
		m.stack_mut().push(SymWord::Concrete(b)).unwrap();

		m.step().unwrap();

		assert_eq!(
			m.stack().peek(0).unwrap(),
			SymWord::Concrete(H256::from_low_u64_be(256))
		);
	}

	#[test]
	fn test_concrete_symbolic_add() {
		let a = H256::from_low_u64_be(255);
		let b = Term::Variable("b".into());

		let code: Vec<u8> = vec![Opcode::ADD.0];

		let stack_limit = 1024;
		let memory_limit = 10000;

		let mut m = Machine::new_symbolic(
			Rc::new(code),
			SymbolicCalldata::default(),
			stack_limit,
			memory_limit,
		);

		m.stack_mut().push(SymWord::Concrete(a)).unwrap();
		m.stack_mut().push(SymWord::Symbolic(b.clone())).unwrap();

		m.step().unwrap();

		assert_eq!(
			m.stack().peek(0).unwrap(),
			SymWord::Symbolic(BvOp::BvAdd(smallvec![b, bv_constant_from_h256(&a)]).into())
		);
	}
}
