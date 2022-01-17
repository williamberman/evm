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
use crate::eval::misc::sym::SymJumpResult;
pub use crate::memory::Memory;
pub use crate::opcode::Opcode;
pub use crate::stack::Stack;
pub use crate::symbolic::{parse_calldata_let, Solution};
pub use crate::valids::Valids;

use crate::eval::Control;
use alloc::vec::Vec;
use amzn_smt_ir::logic::ALL;
use amzn_smt_ir::{Command, CoreOp, Identifier, Index, Script, Sort, Term, UF};
use core::ops::Range;
pub use eval::{htu, uth, DispatchTable, CONCRETE_TABLE, SYMBOLIC_TABLE};
use memory::{ConcreteMemory, MemoryItem, SymbolicMemory};
use num::bigint::ToBigUint;
use primitive_types::{H256, U256};
use stack::StackItem;
use std::convert::TryFrom;
use symbolic::bv_256_n;
pub use symbolic_calldata::SymbolicCalldata;

use smallvec::smallvec;
pub use symbolic::{SymByte, SymWord};

pub type ConcreteMachine = Machine<H256, Vec<u8>, u8, u8>;
pub type SymbolicMachine = Machine<SymWord, SymbolicCalldata, SymByte, SymByte>;

pub trait CodeItem: Into<Opcode> + Clone {}
impl CodeItem for SymByte {}
impl CodeItem for u8 {}

pub trait Calldata: Clone {}
impl<T: Clone> Calldata for T {}

/// Core execution layer for EVM.
#[derive(Clone)]
pub struct Machine<
	IStackItem: StackItem,
	ICalldata: Calldata,
	IMemoryItem: MemoryItem,
	ICodeItem: CodeItem,
> {
	/// Program data.
	data: ICalldata,
	/// Program code.
	code: Vec<ICodeItem>,
	/// Program counter.
	position: Result<usize, ExitReason>,
	/// Return value.
	return_range: Range<U256>,
	/// Code validity maps.
	valids: Valids,
	/// Memory.
	memory: Memory<IMemoryItem>,
	/// Stack.
	stack: Stack<IStackItem>,

	table: DispatchTable<IStackItem, ICalldata, IMemoryItem, ICodeItem>,

	// TODO not used on concrete machine
	pub constraints: Vec<Term>,
}

impl ConcreteMachine {
	pub fn new(code: Vec<u8>, data: Vec<u8>, stack_limit: usize, memory_limit: usize) -> Self {
		let valids = Valids::from(&code[..]);

		Self::internal_new(
			code,
			data,
			stack_limit,
			ConcreteMemory::new(memory_limit),
			valids,
			CONCRETE_TABLE,
		)
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

		match self.code.get(position).map(|v| {
			let v: Opcode = (*v).clone().into();
			v
		}) {
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

	/// Copy and get the return value of the machine, if any.
	pub fn return_value(&self) -> Vec<u8> {
		if self.return_range.start > U256::from(usize::MAX) {
			let mut ret = Vec::new();
			ret.resize(
				(self.return_range.end - self.return_range.start).as_usize(),
				self.memory.default_value.clone(),
			);
			ret
		} else if self.return_range.end > U256::from(usize::MAX) {
			let mut ret = self.memory.get(
				self.return_range.start.as_usize(),
				usize::MAX - self.return_range.start.as_usize(),
			);
			while ret.len() < (self.return_range.end - self.return_range.start).as_usize() {
				ret.push(self.memory.default_value.clone());
			}
			ret
		} else {
			self.memory.get(
				self.return_range.start.as_usize(),
				(self.return_range.end - self.return_range.start).as_usize(),
			)
		}
	}
}

impl SymbolicMachine {
	pub fn new(
		code: Vec<SymByte>,
		data: SymbolicCalldata,
		stack_limit: usize,
		memory_limit: usize,
	) -> Self {
		let valids = Valids::from(&code[..]);

		Self::internal_new(
			code,
			data,
			stack_limit,
			SymbolicMemory::new(memory_limit),
			valids,
			SYMBOLIC_TABLE,
		)
	}

	#[inline]
	pub fn step(
		&mut self,
	) -> (
		Result<(), Capture<ExitReason, Trap>>,
		Vec<(Self, Result<(), Capture<ExitReason, Trap>>)>,
	) {
		let position = self
			.position
			.as_ref()
			.map_err(|reason| Capture::Exit(reason.clone()));

		let position = match position {
			Ok(position) => *position,
			Err(e) => return (Err(e), vec![]),
		};

		match self.code.get(position).map(|v| {
			let v: Opcode = (*v).clone().into();
			v
		}) {
			Some(opcode) => {
				if opcode == Opcode::JUMPI {
					let rv = match self::eval::misc::sym::jumpi(self) {
						SymJumpResult::Concrete {
							control,
							takes_jump: _,
						} => {
							let fst = self.process_control(control);

							// println!("");
							// println!("***********");
							// if takes_jump {
							// 	println!("takes jump");
							// } else {
							// 	println!("does not take jump");
							// }
							// self.debug();
							// println!("***********");

							(fst, vec![])
						}
						SymJumpResult::Symbolic {
							does_not_take_jump,
							mut does_take_jump,
						} => {
							let fst = self.process_control(does_not_take_jump);

							// println!("");
							// println!("***********");
							// println!("does not take jump");
							// self.debug();
							// println!("***********");

							let snd = does_take_jump.0.process_control(does_take_jump.1);

							// println!("***********");
							// println!("takes jump");
							// does_take_jump.0.debug();
							// println!("***********");

							(fst, vec![(does_take_jump.0, snd)])
						}
					};
					println!("");
					rv
				} else {
					let control = self.table[opcode.as_usize()](self, opcode, position);
					(self.process_control(control), vec![])
				}
			}
			None => {
				self.position = Err(ExitSucceed::Stopped.into());
				(Err(Capture::Exit(ExitSucceed::Stopped.into())), vec![])
			}
		}
	}

	pub fn debug(&self) {
		let (opcode, stack) = self.inspect().unwrap();
		println!(
			"PC: {} Opcode: {} Stack: {:?}",
			self.position().as_ref().unwrap(),
			opcode,
			stack
		);
	}

	pub fn process_control(&mut self, c: Control) -> Result<(), Capture<ExitReason, Trap>> {
		let position = *self
			.position
			.as_ref()
			.map_err(|reason| Capture::Exit(reason.clone()))?;

		match c {
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
		}
	}

	pub fn solve(&self) -> Vec<u8> {
		let script = self.script();

		let sol = Solution::try_from(script).unwrap();

		// This is a hack because we know the indices we're solving for
		// in our calldata. Generalizing this shouldn't be hard.

		let a = sol.get_hexadecimal(&Term::Variable("a".into()));
		let b = sol.get_hexadecimal(&Term::Variable("b".into()));
		let c = sol.get_hexadecimal(&Term::Variable("c".into()));
		let d = sol.get_hexadecimal(&Term::Variable("d".into()));

		let nb = if let SymWord::Concrete(n) = self.data.n_bytes {
			htu(&n).as_usize() / 8
		} else {
			panic!("need concrete length")
		};

		let mut rv = vec![0_u8; nb];

		rv[0] = self.data.get_byte(0);
		rv[1] = self.data.get_byte(1);
		rv[2] = self.data.get_byte(2);
		rv[3] = self.data.get_byte(3);

		rv[34] = a[0] * 16 + a[1];
		rv[35] = b[0] * 16 + b[1];
		rv[66] = c[0] * 16 + c[1];
		rv[67] = d[0] * 16 + d[1];

		rv
	}

	pub fn script(&self) -> Script<Term> {
		let mut s = Script::new();

		s.push(Command::<Term>::DeclareFun {
			symbol: "calldata".into(),
			parameters: vec![Sort::Simple {
				identifier: Identifier::Indexed {
					symbol: "BitVec".into(),
					indices: vec![Index::Numeral(256.to_biguint().unwrap())],
				}
				.into(),
			}
			.into()],
			sort: Sort::Simple {
				identifier: Identifier::Indexed {
					symbol: "BitVec".into(),
					indices: vec![Index::Numeral(8.to_biguint().unwrap())],
				}
				.into(),
			}
			.into(),
		});

		s.add_asserts(self.constraints.clone());

		// This is a hack to make the output easily parseable. There's probably
		// a better solution.
		let a = self.declare_in_calldata("a", 34);
		let b = self.declare_in_calldata("b", 35);
		let c = self.declare_in_calldata("c", 66);
		let d = self.declare_in_calldata("d", 67);

		// Check satisfiable and get solution
		s.extend(vec![
			a.1,
			a.2,
			b.1,
			b.2,
			c.1,
			c.2,
			d.1,
			d.2,
			Command::CheckSat,
			Command::GetValue {
				terms: vec![
					// Temp to avoid parsing returned calldata as array
					// Term::Variable("calldata".into())
					a.0, b.0, c.0, d.0,
				],
			},
			Command::Exit,
		]);

		s
	}

	fn declare_in_calldata(&self, s: &str, n: u8) -> (Term, Command<Term>, Command<Term>) {
		let decl: Command<Term> = Command::DeclareConst {
			symbol: s.into(),
			sort: Sort::Simple {
				identifier: Identifier::Indexed {
					symbol: "BitVec".into(),
					indices: vec![Index::Numeral(8.to_biguint().unwrap())],
				}
				.into(),
			}
			.into(),
		};

		let uf = Term::<ALL>::UF(
			UF {
				func: "calldata".into(),
				args: Box::new([bv_256_n(n)]),
			}
			.into(),
		);

		let t = Term::Variable(s.into());

		let xeq: Command<Term> = Command::Assert {
			term: CoreOp::Eq(smallvec![t.clone(), uf]).into(),
		};

		(t, decl, xeq)
	}

	pub fn return_value(&self) -> Vec<u8> {
		let syms = if self.return_range.start > U256::from(usize::MAX) {
			let mut ret = Vec::new();
			ret.resize(
				(self.return_range.end - self.return_range.start).as_usize(),
				self.memory.default_value.clone(),
			);
			ret
		} else if self.return_range.end > U256::from(usize::MAX) {
			let mut ret = self.memory.get(
				self.return_range.start.as_usize(),
				usize::MAX - self.return_range.start.as_usize(),
			);
			while ret.len() < (self.return_range.end - self.return_range.start).as_usize() {
				ret.push(self.memory.default_value.clone());
			}
			ret
		} else {
			self.memory.get(
				self.return_range.start.as_usize(),
				(self.return_range.end - self.return_range.start).as_usize(),
			)
		};
		syms.into_iter()
			.map(|x| match x {
				symbolic::Sym::Concrete(x) => x,
				symbolic::Sym::Symbolic(_) => panic!("need concrete return value"),
			})
			.collect()
	}
}

impl<IStackItem: StackItem, ICalldata: Calldata, IMemoryItem: MemoryItem, ICodeItem: CodeItem>
	Machine<IStackItem, ICalldata, IMemoryItem, ICodeItem>
{
	/// Reference of machine stack.
	pub fn stack(&self) -> &Stack<IStackItem> {
		&self.stack
	}
	/// Mutable reference of machine stack.
	pub fn stack_mut(&mut self) -> &mut Stack<IStackItem> {
		&mut self.stack
	}
	/// Reference of machine memory.
	pub fn memory(&self) -> &Memory<IMemoryItem> {
		&self.memory
	}
	/// Mutable reference of machine memory.
	pub fn memory_mut(&mut self) -> &mut Memory<IMemoryItem> {
		&mut self.memory
	}
	/// Return a reference of the program counter.
	pub fn position(&self) -> &Result<usize, ExitReason> {
		&self.position
	}

	/// Create a new machine with given code and data.
	fn internal_new(
		code: Vec<ICodeItem>,
		data: ICalldata,
		stack_limit: usize,
		memory: Memory<IMemoryItem>,
		valids: Valids,
		table: DispatchTable<IStackItem, ICalldata, IMemoryItem, ICodeItem>,
	) -> Self {
		Self {
			data,
			code,
			position: Ok(0),
			return_range: U256::zero()..U256::zero(),
			valids,
			memory,
			stack: Stack::new(stack_limit),
			table,
			constraints: Vec::new(),
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
		self.code
			.get(position)
			.map(|v| ((*v).clone().into(), &self.stack))
	}
}

#[cfg(test)]
mod tests {
	use crate::{
		symbolic::{bv_constant_from_h256, SymByte},
		Opcode, SymWord, SymbolicCalldata, SymbolicMachine,
	};
	use amzn_smt_ir::{logic::BvOp, Term};
	use primitive_types::H256;
	use smallvec::smallvec;

	#[test]
	fn test_concrete_add() {
		let a = H256::from_low_u64_be(255);
		let b = H256::from_low_u64_be(1);

		let code = vec![SymByte::Concrete(Opcode::ADD.0)];

		let stack_limit = 1024;
		let memory_limit = 10000;

		let mut m =
			SymbolicMachine::new(code, SymbolicCalldata::default(), stack_limit, memory_limit);

		m.stack_mut().push(SymWord::Concrete(a)).unwrap();
		m.stack_mut().push(SymWord::Concrete(b)).unwrap();

		m.step().0.unwrap();

		assert_eq!(
			m.stack().peek(0).unwrap(),
			SymWord::Concrete(H256::from_low_u64_be(256))
		);
	}

	#[test]
	fn test_concrete_symbolic_add() {
		let a = H256::from_low_u64_be(255);
		let b = Term::Variable("b".into());

		let code = vec![SymByte::Concrete(Opcode::ADD.0)];

		let stack_limit = 1024;
		let memory_limit = 10000;

		let mut m =
			SymbolicMachine::new(code, SymbolicCalldata::default(), stack_limit, memory_limit);

		m.stack_mut().push(SymWord::Concrete(a)).unwrap();
		m.stack_mut().push(SymWord::Symbolic(b.clone())).unwrap();

		m.step().0.unwrap();

		assert_eq!(
			m.stack().peek(0).unwrap(),
			SymWord::Symbolic(BvOp::BvAdd(smallvec![b, bv_constant_from_h256(&a)]).into())
		);
	}
}
