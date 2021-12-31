use super::Control;
use crate::{ConcreteMachine, ExitError, ExitFatal, ExitRevert, ExitSucceed, stack::StackItem, memory::MemoryItem, Machine};
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
pub fn dup<IStackItem: StackItem, ICalldata, IMemoryItem: MemoryItem>(
	state: &mut Machine<IStackItem, ICalldata, IMemoryItem>,
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
pub fn swap(state: &mut ConcreteMachine, n: usize) -> Control {
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
	use primitive_types::U256;

	use crate::{
		eval::{htu, uth, Control},
		symbolic::{SymByte, SymWord},
		ExitFatal, SymbolicMachine,
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

		let code: Vec<SymByte> = state
			.code
			.iter()
			.map(|x| SymByte::Concrete(x.clone()))
			.collect();

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
}
