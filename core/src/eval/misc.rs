use super::Control;
use crate::{
	memory::MemoryItem, stack::StackItem, Calldata, CodeItem, ConcreteMachine, ExitError,
	ExitFatal, ExitRevert, ExitSucceed, Machine,
};
use core::cmp::min;
use primitive_types::{H256, U256};

#[inline]
pub fn codesize(state: &mut ConcreteMachine) -> Control {
	let size = U256::from(state.code.len());
	push_u256!(state, size);
	Control::Continue(1)
}

#[inline]
pub fn codecopy(state: &mut ConcreteMachine) -> Control {
	pop_u256!(state, memory_offset, code_offset, len);

	try_or_fail!(state.memory.resize_offset(memory_offset, len));
	match state
		.memory
		.copy_large(memory_offset, code_offset, len, &state.code)
	{
		Ok(()) => Control::Continue(1),
		Err(e) => Control::Exit(e.into()),
	}
}

#[inline]
pub fn calldataload(state: &mut ConcreteMachine) -> Control {
	pop_u256!(state, index);

	let mut load = [0u8; 32];
	#[allow(clippy::needless_range_loop)]
	for i in 0..32 {
		if let Some(p) = index.checked_add(U256::from(i)) {
			if p <= U256::from(usize::MAX) {
				let p = p.as_usize();
				if p < state.data.len() {
					load[i] = state.data[p];
				}
			}
		}
	}

	push!(state, H256::from(load));
	Control::Continue(1)
}

#[inline]
pub fn calldatasize(state: &mut ConcreteMachine) -> Control {
	let len = U256::from(state.data.len());
	push_u256!(state, len);
	Control::Continue(1)
}

#[inline]
pub fn calldatacopy(state: &mut ConcreteMachine) -> Control {
	pop_u256!(state, memory_offset, data_offset, len);

	try_or_fail!(state.memory.resize_offset(memory_offset, len));
	if len == U256::zero() {
		return Control::Continue(1);
	}

	match state
		.memory
		.copy_large(memory_offset, data_offset, len, &state.data)
	{
		Ok(()) => Control::Continue(1),
		Err(e) => Control::Exit(e.into()),
	}
}

#[inline]
pub fn pop(state: &mut ConcreteMachine) -> Control {
	pop!(state, _val);
	Control::Continue(1)
}

#[inline]
pub fn mload(state: &mut ConcreteMachine) -> Control {
	pop_u256!(state, index);
	try_or_fail!(state.memory.resize_offset(index, U256::from(32)));
	let index = as_usize_or_fail!(index);
	let value = H256::from_slice(&state.memory.get(index, 32)[..]);
	push!(state, value);
	Control::Continue(1)
}

#[inline]
pub fn mstore(state: &mut ConcreteMachine) -> Control {
	pop_u256!(state, index);
	pop!(state, value);
	try_or_fail!(state.memory.resize_offset(index, U256::from(32)));
	let index = as_usize_or_fail!(index);
	match state.memory.set(index, &value[..], Some(32)) {
		Ok(()) => Control::Continue(1),
		Err(e) => Control::Exit(e.into()),
	}
}

#[inline]
pub fn mstore8(state: &mut ConcreteMachine) -> Control {
	pop_u256!(state, index, value);
	try_or_fail!(state.memory.resize_offset(index, U256::one()));
	let index = as_usize_or_fail!(index);
	let value = (value.low_u32() & 0xff) as u8;
	match state.memory.set(index, &[value], Some(1)) {
		Ok(()) => Control::Continue(1),
		Err(e) => Control::Exit(e.into()),
	}
}

#[inline]
pub fn jump(state: &mut ConcreteMachine) -> Control {
	pop_u256!(state, dest);
	let dest = as_usize_or_fail!(dest, ExitError::InvalidJump);

	if state.valids.is_valid(dest) {
		Control::Jump(dest)
	} else {
		Control::Exit(ExitError::InvalidJump.into())
	}
}

#[inline]
pub fn jumpi(state: &mut ConcreteMachine) -> Control {
	pop_u256!(state, dest);
	pop!(state, value);

	if value != H256::zero() {
		let dest = as_usize_or_fail!(dest, ExitError::InvalidJump);
		if state.valids.is_valid(dest) {
			Control::Jump(dest)
		} else {
			Control::Exit(ExitError::InvalidJump.into())
		}
	} else {
		Control::Continue(1)
	}
}

#[inline]
pub fn pc(state: &mut ConcreteMachine, position: usize) -> Control {
	push_u256!(state, U256::from(position));
	Control::Continue(1)
}

#[inline]
pub fn msize(state: &mut ConcreteMachine) -> Control {
	push_u256!(state, state.memory.effective_len());
	Control::Continue(1)
}

#[inline]
pub fn push(state: &mut ConcreteMachine, n: usize, position: usize) -> Control {
	let end = min(position + 1 + n, state.code.len());
	let slice = &state.code[(position + 1)..end];
	let mut val = [0u8; 32];
	val[(32 - slice.len())..32].copy_from_slice(slice);

	push!(state, H256(val));
	Control::Continue(1 + n)
}

#[inline]
pub fn dup<
	IStackItem: StackItem,
	ICalldata: Calldata,
	IMemoryItem: MemoryItem,
	ICodeItem: CodeItem,
>(
	state: &mut Machine<IStackItem, ICalldata, IMemoryItem, ICodeItem>,
	n: usize,
) -> Control {
	let value = match state.stack.peek(n - 1) {
		Ok(value) => value,
		Err(e) => return Control::Exit(e.into()),
	};
	push!(state, value);
	Control::Continue(1)
}

#[inline]
pub fn swap<
	IStackItem: StackItem,
	ICalldata: Calldata,
	IMemoryItem: MemoryItem,
	ICodeItem: CodeItem,
>(
	state: &mut Machine<IStackItem, ICalldata, IMemoryItem, ICodeItem>,
	n: usize,
) -> Control {
	let val1 = match state.stack.peek(0) {
		Ok(value) => value,
		Err(e) => return Control::Exit(e.into()),
	};
	let val2 = match state.stack.peek(n) {
		Ok(value) => value,
		Err(e) => return Control::Exit(e.into()),
	};
	match state.stack.set(0, val2) {
		Ok(()) => (),
		Err(e) => return Control::Exit(e.into()),
	}
	match state.stack.set(n, val1) {
		Ok(()) => (),
		Err(e) => return Control::Exit(e.into()),
	}
	Control::Continue(1)
}

#[inline]
pub fn ret(state: &mut ConcreteMachine) -> Control {
	pop_u256!(state, start, len);
	try_or_fail!(state.memory.resize_offset(start, len));
	state.return_range = start..(start + len);
	Control::Exit(ExitSucceed::Returned.into())
}

#[inline]
pub fn revert(state: &mut ConcreteMachine) -> Control {
	pop_u256!(state, start, len);
	try_or_fail!(state.memory.resize_offset(start, len));
	state.return_range = start..(start + len);
	Control::Exit(ExitRevert::Reverted.into())
}

pub mod sym {
	use amzn_smt_ir::{logic::BvOp, CoreOp, Index, Term};
	use num::bigint::ToBigUint;
	use primitive_types::{H256, U256};
	use smallvec::smallvec;

	use crate::{
		eval::{htu, uth, Control},
		symbolic::{bv_256_zero, extract_bytes_to_word, SymByte, SymWord},
		ExitError, ExitFatal, ExitRevert, ExitSucceed, SymbolicMachine,
	};

	pub fn codesize(state: &mut SymbolicMachine) -> Control {
		let size = SymWord::Concrete(uth(&U256::from(state.code.len())));
		push!(state, size);
		Control::Continue(1)
	}

	pub fn codecopy(state: &mut SymbolicMachine) -> Control {
		pop!(state, memory_offset, code_offset, len);

		let (memory_offset, code_offset, len) = match (memory_offset, code_offset, len) {
			(SymWord::Concrete(x), SymWord::Concrete(y), SymWord::Concrete(z)) => {
				(htu(&x), htu(&y), htu(&z))
			}

			_ => panic!("cannot use symbolic args for CODECOPY"),
		};

		let code: Vec<SymByte> = state.code.iter().map(|x| x.clone()).collect();

		try_or_fail!(state.memory.resize_offset(memory_offset, len));
		match state
			.memory
			.copy_large(memory_offset, code_offset, len, &code)
		{
			Ok(()) => Control::Continue(1),
			Err(e) => Control::Exit(e.into()),
		}
	}

	pub fn calldataload(state: &mut SymbolicMachine) -> Control {
		pop!(state, index);

		let ret = state.data.load(index);

		push!(state, ret);

		Control::Continue(1)
	}

	pub fn calldatasize(state: &mut SymbolicMachine) -> Control {
		let len = state.data.n_bytes.clone();
		push!(state, len);
		Control::Continue(1)
	}

	pub fn calldatacopy(state: &mut SymbolicMachine) -> Control {
		pop!(state, memory_offset, data_offset, len);

		let (memory_offset, data_offset, len) = match (memory_offset, data_offset, len) {
			(SymWord::Concrete(x), SymWord::Concrete(y), SymWord::Concrete(z)) => {
				(htu(&x), htu(&y), htu(&z))
			}
			_ => panic!("cannot use symbolic args for CALLDATACOPY"),
		};

		try_or_fail!(state.memory.resize_offset(memory_offset, len));
		if len == U256::zero() {
			return Control::Continue(1);
		}

		match state
			.memory
			.copy_large_symbolic(memory_offset, data_offset, len, &state.data)
		{
			Ok(()) => Control::Continue(1),
			Err(e) => Control::Exit(e.into()),
		}
	}

	pub fn pop(state: &mut SymbolicMachine) -> Control {
		pop!(state, _val);
		Control::Continue(1)
	}

	pub fn mload(state: &mut SymbolicMachine) -> Control {
		pop!(state, index);

		let index = match index {
			SymWord::Concrete(x) => htu(&x),
			_ => panic!("cannot use symbolic args for MLOAD"),
		};

		try_or_fail!(state.memory.resize_offset(index, U256::from(32)));
		let index = as_usize_or_fail!(index);
		let value = state.memory.get_word(index);
		push!(state, value);
		Control::Continue(1)
	}

	pub fn pc(state: &mut SymbolicMachine, position: usize) -> Control {
		let ret = SymWord::Concrete(uth(&U256::from(position)));
		push!(state, ret);
		Control::Continue(1)
	}

	pub fn msize(state: &mut SymbolicMachine) -> Control {
		let ret = SymWord::Concrete(uth(&state.memory.effective_len()));
		push!(state, ret);
		Control::Continue(1)
	}

	pub fn jump(state: &mut SymbolicMachine) -> Control {
		pop!(state, dest);

		let dest = match dest {
			SymWord::Concrete(x) => htu(&x),
			_ => panic!("cannot use symbolic arg for JUMP"),
		};

		let dest = as_usize_or_fail!(dest, ExitError::InvalidJump);

		if state.valids.is_valid(dest) {
			Control::Jump(dest)
		} else {
			Control::Exit(ExitError::InvalidJump.into())
		}
	}

	pub fn mstore(state: &mut SymbolicMachine) -> Control {
		pop!(state, index, value);

		let index = match index {
			SymWord::Concrete(x) => htu(&x),
			_ => panic!("cannot use symbolic index for MSTORE"),
		};

		try_or_fail!(state.memory.resize_offset(index, U256::from(32)));
		let index = as_usize_or_fail!(index);

		let bytes = match value {
			SymWord::Concrete(x) => x
				.as_bytes()
				.iter()
				.map(|b| SymByte::Concrete(b.clone()))
				.collect::<Vec<SymByte>>(),
			SymWord::Symbolic(x) => {
				// Extract bytes at bit indices from highest to lowest
				//
				// extract(255, 248)
				// extract(247, 240)
				// ...
				// extract(7, 0)
				(0..=31)
					.rev()
					.map(|i| {
						let low_bit_index = i * 31;
						let high_bit_index = low_bit_index + 7;

						SymByte::Symbolic(
							BvOp::Extract(
								[
									Index::Numeral(high_bit_index.to_biguint().unwrap()).into(),
									Index::Numeral(low_bit_index.to_biguint().unwrap()).into(),
								],
								x.clone(),
							)
							.into(),
						)
					})
					.collect()
			}
		};

		match state.memory.set(index, &bytes[..], Some(32)) {
			Ok(()) => Control::Continue(1),
			Err(e) => Control::Exit(e.into()),
		}
	}

	pub fn mstore8(state: &mut SymbolicMachine) -> Control {
		pop!(state, index, value);

		let index = match index {
			SymWord::Concrete(x) => htu(&x),
			_ => panic!("cannot use symbolic index for MSTORE"),
		};

		try_or_fail!(state.memory.resize_offset(index, U256::one()));

		let index = as_usize_or_fail!(index);

		let byte = match value {
			SymWord::Concrete(x) => SymByte::Concrete(x.as_bytes()[31]),
			SymWord::Symbolic(x) => {
				// Extract just the lowest byte
				SymByte::Symbolic(
					BvOp::Extract(
						[
							Index::Numeral(7.to_biguint().unwrap()).into(),
							Index::Numeral(0.to_biguint().unwrap()).into(),
						],
						x.clone(),
					)
					.into(),
				)
			}
		};

		match state.memory.set(index, &[byte], Some(1)) {
			Ok(()) => Control::Continue(1),
			Err(e) => Control::Exit(e.into()),
		}
	}

	pub fn push(state: &mut SymbolicMachine, n: usize, position: usize) -> Control {
		let read_from_offset = position + 1;

		let extract_n_bytes = if read_from_offset + n > state.code.len() {
			state.code.len() - read_from_offset
		} else {
			n
		};

		let ret = extract_bytes_to_word(&state.code, read_from_offset, extract_n_bytes, false);

		push!(state, ret);

		Control::Continue(1 + n)
	}

	pub fn ret(state: &mut SymbolicMachine) -> Control {
		pop!(state, start, len);

		let (start, len) = match (start, len) {
			(SymWord::Concrete(start), SymWord::Concrete(len)) => (htu(&start), htu(&len)),
			_ => panic!("cannot use symbolic arguments for RETURN"),
		};

		try_or_fail!(state.memory.resize_offset(start, len));
		state.return_range = start..(start + len);
		Control::Exit(ExitSucceed::Returned.into())
	}

	pub fn revert(state: &mut SymbolicMachine) -> Control {
		pop!(state, start, len);

		let (start, len) = match (start, len) {
			(SymWord::Concrete(start), SymWord::Concrete(len)) => (htu(&start), htu(&len)),
			_ => panic!("cannot use symbolic arguments for REVERT"),
		};

		try_or_fail!(state.memory.resize_offset(start, len));
		state.return_range = start..(start + len);

		Control::Exit(ExitRevert::Reverted.into())
	}

	enum J {
		Takes,
		Not,
	}

	// TODO(will) remove and instead know the 
	// exit code to look for
	static JS: [J; 12] = [
		J::Takes,
		J::Not,
		J::Takes,
		J::Takes,
		J::Takes,
		J::Takes,
		J::Not,
		J::Not,
		J::Not,
		J::Takes,
		J::Takes,
		J::Not,
	];

	pub enum SymJumpResult {
		Concrete {
			control: Control,
			takes_jump: bool,
		},
		#[allow(dead_code)]
		Symbolic {
			does_not_take_jump: Control,
			does_take_jump: (SymbolicMachine, Control),
		},
	}

	pub fn jumpi(state: &mut SymbolicMachine) -> SymJumpResult {
		let j = JS.get(state.jumps).unwrap();
		state.jumps += 1;

		let dest = match state.stack.pop() {
			Ok(value) => value,
			Err(e) => {
				return SymJumpResult::Concrete {
					control: Control::Exit(e.into()),
					takes_jump: false,
				}
			}
		};

		let value = match state.stack.pop() {
			Ok(value) => value,
			Err(e) => {
				return SymJumpResult::Concrete {
					control: Control::Exit(e.into()),
					takes_jump: false,
				}
			}
		};

		let dest = match dest {
			SymWord::Concrete(dest) => htu(&dest),
			SymWord::Symbolic(_) => panic!("cannot use symbolic dest for JUMPI"),
		};

		if dest > U256::from(usize::MAX) {
			return SymJumpResult::Concrete {
				control: Control::Exit(ExitError::InvalidJump.into()),
				takes_jump: false,
			};
		}

		let dest = dest.as_usize();

		match value {
			SymWord::Concrete(value) => {
				let (control, takes_jump) = if value != H256::zero() {
					if state.valids.is_valid(dest) {
						(Control::Jump(dest), true)
					} else {
						(Control::Exit(ExitError::InvalidJump.into()), false)
					}
				} else {
					(Control::Continue(1), false)
				};

				return SymJumpResult::Concrete {
					control,
					takes_jump,
				};
			}
			SymWord::Symbolic(value) => {
				let (control, takes_jump) = match j {
					J::Takes => {
						(take_jump(state, dest, value), true)
					}
					J::Not => {
						(no_take_jump(state, value), false)
					}
				};

				SymJumpResult::Concrete {
					control,
					takes_jump
				}

				// let mut takes_jump = state.clone();
				// let takes_jump_c = take_jump(&mut takes_jump, dest, value.clone());

				// SymJumpResult::Symbolic {
				// 	does_not_take_jump: no_take_jump(state, value),
				// 	does_take_jump: (takes_jump, takes_jump_c),
				// }
			}
		}
	}

	fn take_jump(state: &mut SymbolicMachine, dest: usize, value: Term) -> Control {
		let does_not_take_jump_constraint: Term =
			CoreOp::Eq(smallvec![value.clone(), bv_256_zero()]).into();

		let takes_jump_constraint: Term = CoreOp::Not(does_not_take_jump_constraint.clone()).into();

		state.constraints.push(takes_jump_constraint);

		if state.valids.is_valid(dest) {
			Control::Jump(dest)
		} else {
			Control::Exit(ExitError::InvalidJump.into())
		}
	}

	fn no_take_jump(state: &mut SymbolicMachine, value: Term) -> Control {
		let does_not_take_jump_constraint: Term =
			CoreOp::Eq(smallvec![value.clone(), bv_256_zero()]).into();

		state.constraints.push(does_not_take_jump_constraint);

		Control::Continue(1)
	}
}
