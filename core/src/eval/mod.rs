#[macro_use]
mod macros;
mod arithmetic;
mod bitwise;
mod misc;

use crate::{
	memory::MemoryItem,
	stack::StackItem,
	symbolic::{self, bv_256_one, bv_256_zero, SymByte, SymWord},
	ConcreteMachine, ExitError, ExitReason, ExitSucceed, Machine, Opcode, SymbolicCalldata,
	SymbolicMachine,
};
use amzn_smt_ir::{logic::BvOp, CoreOp};
use core::ops::{BitAnd, BitOr, BitXor};
use primitive_types::{H256, U256};
use smallvec::smallvec;

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Control {
	Continue(usize),
	Exit(ExitReason),
	Jump(usize),
	Trap(Opcode),
}

type OpEval<IStackItem, ICalldata, IMemoryItem> = fn(
	state: &mut Machine<IStackItem, ICalldata, IMemoryItem>,
	opcode: Opcode,
	position: usize,
) -> Control;

struct OpEvals {
	concrete: OpEval<H256, Vec<u8>, u8>,
	symbolic: OpEval<SymWord, SymbolicCalldata, SymByte>,
}

pub fn htu(h: &H256) -> U256 {
	U256::from_big_endian(&h[..])
}

pub fn uth(u: &U256) -> H256 {
	let mut rv = H256::default();
	u.to_big_endian(&mut rv[..]);
	rv
}

fn eval_stop<IStackItem: StackItem, ICalldata, IMemoryItem: MemoryItem>(
	_state: &mut Machine<IStackItem, ICalldata, IMemoryItem>,
	_opcode: Opcode,
	_position: usize,
) -> Control {
	Control::Exit(ExitSucceed::Stopped.into())
}

op2_evals_tuple_vec!(ADD, overflowing_add, BvOp::BvAdd);
op2_evals_tuple_vec!(MUL, overflowing_mul, BvOp::BvMul);
op2_evals_tuple!(SUB, overflowing_sub, BvOp::BvSub);
op2_evals_fn!(DIV, self::arithmetic::div, BvOp::BvUdiv);
op2_evals_fn!(SDIV, self::arithmetic::sdiv, BvOp::BvSdiv);
op2_evals_fn!(MOD, self::arithmetic::rem, BvOp::BvUrem);
op2_evals_fn!(SMOD, self::arithmetic::srem, BvOp::BvSrem);

static ADDMOD: OpEvals = OpEvals {
	concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| -> Control {
		op3_u256_fn!(state, self::arithmetic::addmod)
	},

	symbolic: |state: &mut SymbolicMachine, _opcode: Opcode, _position: usize| -> Control {
		self::arithmetic::sym::addmod(state)
	},
};

static MULMOD: OpEvals = OpEvals {
	concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| -> Control {
		op3_u256_fn!(state, self::arithmetic::mulmod)
	},

	symbolic: |state: &mut SymbolicMachine, _opcode: Opcode, _position: usize| -> Control {
		self::arithmetic::sym::mulmod(state)
	},
};

fn eval_exp(state: &mut ConcreteMachine, _opcode: Opcode, _position: usize) -> Control {
	op2_u256_fn!(state, self::arithmetic::exp)
}

static SIGNEXTEND: OpEvals = OpEvals {
	concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| -> Control {
		op2_u256_fn!(state, self::arithmetic::signextend)
	},
	symbolic: |state: &mut SymbolicMachine, _opcode: Opcode, _position: usize| -> Control {
		self::arithmetic::sym::signextend(state)
	},
};

op2_evals_bool_tuple!(LT, lt, BvOp::BvUlt);
op2_evals_bool_tuple!(GT, gt, BvOp::BvUgt);
op2_evals_bool_fn!(SLT, self::bitwise::slt, BvOp::BvSlt);
op2_evals_bool_fn!(SGT, self::bitwise::sgt, BvOp::BvSgt);
op2_evals_bool_tuple_vec!(EQ, eq, CoreOp::Eq);

static ISZERO: OpEvals = OpEvals {
	concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| -> Control {
		op1_u256_fn!(state, self::bitwise::iszero)
	},
	symbolic: |state: &mut SymbolicMachine, _opcode: Opcode, _position: usize| -> Control {
		self::bitwise::sym::iszero(state)
	},
};

op2_evals_x_vec!(AND, bitand, BvOp::BvAnd);
op2_evals_x_vec!(OR, bitor, BvOp::BvOr);
op2_evals_x_vec!(XOR, bitxor, BvOp::BvXor);

static NOT: OpEvals = OpEvals {
	concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| -> Control {
		op1_u256_fn!(state, self::bitwise::not)
	},
	symbolic: |state: &mut SymbolicMachine, _opcode: Opcode, _position: usize| -> Control {
		self::bitwise::sym::not(state)
	},
};

fn eval_byte(state: &mut ConcreteMachine, _opcode: Opcode, _position: usize) -> Control {
	op2_u256_fn!(state, self::bitwise::byte)
}

op2_evals_fn!(SHL, self::bitwise::shl, BvOp::BvShl);
op2_evals_fn!(SHR, self::bitwise::shr, BvOp::BvLshr);
op2_evals_fn!(SAR, self::bitwise::sar, BvOp::BvAshr);

static CODESIZE: OpEvals = OpEvals {
	concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| -> Control {
		self::misc::codesize(state)
	},
	symbolic: |state: &mut SymbolicMachine, _opcode: Opcode, _position: usize| -> Control {
		self::misc::sym::codesize(state)
	},
};

static CODECOPY: OpEvals = OpEvals {
	concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| -> Control {
		self::misc::codecopy(state)
	},
	symbolic: |state: &mut SymbolicMachine, _opcode: Opcode, _position: usize| -> Control {
		self::misc::sym::codecopy(state)
	},
};

static CALLDATALOAD: OpEvals = OpEvals {
	concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| -> Control {
		self::misc::calldataload(state)
	},

	symbolic: |state: &mut SymbolicMachine, _opcode: Opcode, _position: usize| -> Control {
		self::misc::sym::calldataload(state)
	},
};

static CALLDATASIZE: OpEvals = OpEvals {
	concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| -> Control {
		self::misc::calldatasize(state)
	},

	symbolic: |state: &mut SymbolicMachine, _opcode: Opcode, _position: usize| -> Control {
		self::misc::sym::calldatasize(state)
	},
};

static CALLDATACOPY: OpEvals = OpEvals {
	concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| -> Control {
		self::misc::calldatacopy(state)
	},
	symbolic: |state: &mut SymbolicMachine, _opcode: Opcode, _position: usize| -> Control {
		self::misc::sym::calldatacopy(state)
	},
};

static POP: OpEvals = OpEvals {
	concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| -> Control {
		self::misc::pop(state)
	},
	symbolic: |state: &mut SymbolicMachine, _opcode: Opcode, _position: usize| -> Control {
		self::misc::sym::pop(state)
	},
};

static MLOAD: OpEvals = OpEvals {
	concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| -> Control {
		self::misc::mload(state)
	},
	symbolic: |state: &mut SymbolicMachine, _opcode: Opcode, _position: usize| -> Control {
		self::misc::sym::mload(state)
	},
};

fn eval_mstore(state: &mut ConcreteMachine, _opcode: Opcode, _position: usize) -> Control {
	self::misc::mstore(state)
}

fn eval_mstore8(state: &mut ConcreteMachine, _opcode: Opcode, _position: usize) -> Control {
	self::misc::mstore8(state)
}

fn eval_jump(state: &mut ConcreteMachine, _opcode: Opcode, _position: usize) -> Control {
	self::misc::jump(state)
}

fn eval_jumpi(state: &mut ConcreteMachine, _opcode: Opcode, _position: usize) -> Control {
	self::misc::jumpi(state)
}

static PC: OpEvals = OpEvals {
	concrete: |state: &mut ConcreteMachine, _opcode: Opcode, position: usize| -> Control {
		self::misc::pc(state, position)
	},
	symbolic: |state: &mut SymbolicMachine, _opcode: Opcode, position: usize| -> Control {
		self::misc::sym::pc(state, position)
	},
};

fn eval_msize(state: &mut ConcreteMachine, _opcode: Opcode, _position: usize) -> Control {
	self::misc::msize(state)
}

fn eval_jumpdest<IStackItem: StackItem, ICalldata, IMemoryItem: MemoryItem>(
	_state: &mut Machine<IStackItem, ICalldata, IMemoryItem>,
	_opcode: Opcode,
	_position: usize,
) -> Control {
	Control::Continue(1)
}

fn eval_push1(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 1, position)
}

fn eval_push2(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 2, position)
}

fn eval_push3(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 3, position)
}

fn eval_push4(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 4, position)
}

fn eval_push5(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 5, position)
}

fn eval_push6(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 6, position)
}

fn eval_push7(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 7, position)
}

fn eval_push8(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 8, position)
}

fn eval_push9(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 9, position)
}

fn eval_push10(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 10, position)
}

fn eval_push11(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 11, position)
}

fn eval_push12(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 12, position)
}

fn eval_push13(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 13, position)
}

fn eval_push14(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 14, position)
}

fn eval_push15(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 15, position)
}

fn eval_push16(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 16, position)
}

fn eval_push17(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 17, position)
}

fn eval_push18(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 18, position)
}

fn eval_push19(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 19, position)
}

fn eval_push20(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 20, position)
}

fn eval_push21(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 21, position)
}

fn eval_push22(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 22, position)
}

fn eval_push23(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 23, position)
}

fn eval_push24(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 24, position)
}

fn eval_push25(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 25, position)
}

fn eval_push26(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 26, position)
}

fn eval_push27(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 27, position)
}

fn eval_push28(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 28, position)
}

fn eval_push29(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 29, position)
}

fn eval_push30(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 30, position)
}

fn eval_push31(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 31, position)
}

fn eval_push32(state: &mut ConcreteMachine, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 32, position)
}

dup_op!(DUP1, 1);
dup_op!(DUP2, 2);
dup_op!(DUP3, 3);
dup_op!(DUP4, 4);
dup_op!(DUP5, 5);
dup_op!(DUP6, 6);
dup_op!(DUP7, 7);
dup_op!(DUP8, 8);
dup_op!(DUP9, 9);
dup_op!(DUP10, 10);
dup_op!(DUP11, 11);
dup_op!(DUP12, 12);
dup_op!(DUP13, 13);
dup_op!(DUP14, 14);
dup_op!(DUP15, 15);
dup_op!(DUP16, 16);

swap_op!(SWAP1, 1);
swap_op!(SWAP2, 2);
swap_op!(SWAP3, 3);
swap_op!(SWAP4, 4);
swap_op!(SWAP5, 5);
swap_op!(SWAP6, 6);
swap_op!(SWAP7, 7);
swap_op!(SWAP8, 8);
swap_op!(SWAP9, 9);
swap_op!(SWAP10, 10);
swap_op!(SWAP11, 11);
swap_op!(SWAP12, 12);
swap_op!(SWAP13, 13);
swap_op!(SWAP14, 14);
swap_op!(SWAP15, 15);
swap_op!(SWAP16, 16);

fn eval_return(state: &mut ConcreteMachine, _opcode: Opcode, _position: usize) -> Control {
	self::misc::ret(state)
}

fn eval_revert(state: &mut ConcreteMachine, _opcode: Opcode, _position: usize) -> Control {
	self::misc::revert(state)
}

same_op!(INVALID, Control::Exit(ExitError::DesignatedInvalid.into()));

static EXTERNAL: OpEvals = OpEvals {
	concrete: |_state: &mut ConcreteMachine, opcode: Opcode, _position: usize| -> Control {
		Control::Trap(opcode)
	},
	symbolic: |_state: &mut SymbolicMachine, opcode: Opcode, _position: usize| -> Control {
		Control::Trap(opcode)
	},
};

pub type DispatchTable<IStackItem, ICalldata, IMemoryItem> = [fn(
	state: &mut Machine<IStackItem, ICalldata, IMemoryItem>,
	opcode: Opcode,
	position: usize,
) -> Control; 256];

pub static CONCRETE_TABLE: DispatchTable<H256, Vec<u8>, u8> = {
	let mut table = [EXTERNAL.concrete as _; 256];

	table[Opcode::STOP.as_usize()] = eval_stop as _;
	table[Opcode::ADD.as_usize()] = ADD.concrete as _;
	table[Opcode::MUL.as_usize()] = MUL.concrete as _;
	table[Opcode::SUB.as_usize()] = SUB.concrete as _;
	table[Opcode::DIV.as_usize()] = DIV.concrete as _;
	table[Opcode::SDIV.as_usize()] = SDIV.concrete as _;
	table[Opcode::MOD.as_usize()] = MOD.concrete as _;
	table[Opcode::SMOD.as_usize()] = SMOD.concrete as _;
	table[Opcode::ADDMOD.as_usize()] = ADDMOD.concrete as _;
	table[Opcode::MULMOD.as_usize()] = MULMOD.concrete as _;
	table[Opcode::EXP.as_usize()] = eval_exp as _;
	table[Opcode::SIGNEXTEND.as_usize()] = SIGNEXTEND.concrete as _;
	table[Opcode::LT.as_usize()] = LT.concrete as _;
	table[Opcode::GT.as_usize()] = GT.concrete as _;
	table[Opcode::SLT.as_usize()] = SLT.concrete as _;
	table[Opcode::SGT.as_usize()] = SGT.concrete as _;
	table[Opcode::EQ.as_usize()] = EQ.concrete as _;
	table[Opcode::ISZERO.as_usize()] = ISZERO.concrete as _;
	table[Opcode::AND.as_usize()] = AND.concrete as _;
	table[Opcode::OR.as_usize()] = OR.concrete as _;
	table[Opcode::XOR.as_usize()] = XOR.concrete as _;
	table[Opcode::NOT.as_usize()] = NOT.concrete as _;
	table[Opcode::BYTE.as_usize()] = eval_byte as _;
	table[Opcode::SHL.as_usize()] = SHL.concrete as _;
	table[Opcode::SHR.as_usize()] = SHR.concrete as _;
	table[Opcode::SAR.as_usize()] = SAR.concrete as _;
	table[Opcode::CODESIZE.as_usize()] = CODESIZE.concrete as _;
	table[Opcode::CODECOPY.as_usize()] = CODECOPY.concrete as _;
	table[Opcode::CALLDATALOAD.as_usize()] = CALLDATALOAD.concrete as _;
	table[Opcode::CALLDATASIZE.as_usize()] = CALLDATASIZE.concrete as _;
	table[Opcode::CALLDATACOPY.as_usize()] = CALLDATACOPY.concrete as _;
	table[Opcode::POP.as_usize()] = POP.concrete as _;
	table[Opcode::MLOAD.as_usize()] = MLOAD.concrete as _;
	table[Opcode::MSTORE.as_usize()] = eval_mstore as _;
	table[Opcode::MSTORE8.as_usize()] = eval_mstore8 as _;
	table[Opcode::JUMP.as_usize()] = eval_jump as _;
	table[Opcode::JUMPI.as_usize()] = eval_jumpi as _;
	table[Opcode::PC.as_usize()] = PC.concrete as _;
	table[Opcode::MSIZE.as_usize()] = eval_msize as _;
	table[Opcode::JUMPDEST.as_usize()] = eval_jumpdest as _;

	table[Opcode::PUSH1.as_usize()] = eval_push1 as _;
	table[Opcode::PUSH2.as_usize()] = eval_push2 as _;
	table[Opcode::PUSH3.as_usize()] = eval_push3 as _;
	table[Opcode::PUSH4.as_usize()] = eval_push4 as _;
	table[Opcode::PUSH5.as_usize()] = eval_push5 as _;
	table[Opcode::PUSH6.as_usize()] = eval_push6 as _;
	table[Opcode::PUSH7.as_usize()] = eval_push7 as _;
	table[Opcode::PUSH8.as_usize()] = eval_push8 as _;
	table[Opcode::PUSH9.as_usize()] = eval_push9 as _;
	table[Opcode::PUSH10.as_usize()] = eval_push10 as _;
	table[Opcode::PUSH11.as_usize()] = eval_push11 as _;
	table[Opcode::PUSH12.as_usize()] = eval_push12 as _;
	table[Opcode::PUSH13.as_usize()] = eval_push13 as _;
	table[Opcode::PUSH14.as_usize()] = eval_push14 as _;
	table[Opcode::PUSH15.as_usize()] = eval_push15 as _;
	table[Opcode::PUSH16.as_usize()] = eval_push16 as _;
	table[Opcode::PUSH17.as_usize()] = eval_push17 as _;
	table[Opcode::PUSH18.as_usize()] = eval_push18 as _;
	table[Opcode::PUSH19.as_usize()] = eval_push19 as _;
	table[Opcode::PUSH20.as_usize()] = eval_push20 as _;
	table[Opcode::PUSH21.as_usize()] = eval_push21 as _;
	table[Opcode::PUSH22.as_usize()] = eval_push22 as _;
	table[Opcode::PUSH23.as_usize()] = eval_push23 as _;
	table[Opcode::PUSH24.as_usize()] = eval_push24 as _;
	table[Opcode::PUSH25.as_usize()] = eval_push25 as _;
	table[Opcode::PUSH26.as_usize()] = eval_push26 as _;
	table[Opcode::PUSH27.as_usize()] = eval_push27 as _;
	table[Opcode::PUSH28.as_usize()] = eval_push28 as _;
	table[Opcode::PUSH29.as_usize()] = eval_push29 as _;
	table[Opcode::PUSH30.as_usize()] = eval_push30 as _;
	table[Opcode::PUSH31.as_usize()] = eval_push31 as _;
	table[Opcode::PUSH32.as_usize()] = eval_push32 as _;

	table[Opcode::DUP1.as_usize()] = DUP1.concrete as _;
	table[Opcode::DUP2.as_usize()] = DUP2.concrete as _;
	table[Opcode::DUP3.as_usize()] = DUP3.concrete as _;
	table[Opcode::DUP4.as_usize()] = DUP4.concrete as _;
	table[Opcode::DUP5.as_usize()] = DUP5.concrete as _;
	table[Opcode::DUP6.as_usize()] = DUP6.concrete as _;
	table[Opcode::DUP7.as_usize()] = DUP7.concrete as _;
	table[Opcode::DUP8.as_usize()] = DUP8.concrete as _;
	table[Opcode::DUP9.as_usize()] = DUP9.concrete as _;
	table[Opcode::DUP10.as_usize()] = DUP10.concrete as _;
	table[Opcode::DUP11.as_usize()] = DUP11.concrete as _;
	table[Opcode::DUP12.as_usize()] = DUP12.concrete as _;
	table[Opcode::DUP13.as_usize()] = DUP13.concrete as _;
	table[Opcode::DUP14.as_usize()] = DUP14.concrete as _;
	table[Opcode::DUP15.as_usize()] = DUP15.concrete as _;
	table[Opcode::DUP16.as_usize()] = DUP16.concrete as _;

	table[Opcode::SWAP1.as_usize()] = SWAP1.concrete as _;
	table[Opcode::SWAP2.as_usize()] = SWAP2.concrete as _;
	table[Opcode::SWAP3.as_usize()] = SWAP3.concrete as _;
	table[Opcode::SWAP4.as_usize()] = SWAP4.concrete as _;
	table[Opcode::SWAP5.as_usize()] = SWAP5.concrete as _;
	table[Opcode::SWAP6.as_usize()] = SWAP6.concrete as _;
	table[Opcode::SWAP7.as_usize()] = SWAP7.concrete as _;
	table[Opcode::SWAP8.as_usize()] = SWAP8.concrete as _;
	table[Opcode::SWAP9.as_usize()] = SWAP9.concrete as _;
	table[Opcode::SWAP10.as_usize()] = SWAP10.concrete as _;
	table[Opcode::SWAP11.as_usize()] = SWAP11.concrete as _;
	table[Opcode::SWAP12.as_usize()] = SWAP12.concrete as _;
	table[Opcode::SWAP13.as_usize()] = SWAP13.concrete as _;
	table[Opcode::SWAP14.as_usize()] = SWAP14.concrete as _;
	table[Opcode::SWAP15.as_usize()] = SWAP15.concrete as _;
	table[Opcode::SWAP16.as_usize()] = SWAP16.concrete as _;

	table[Opcode::RETURN.as_usize()] = eval_return as _;
	table[Opcode::REVERT.as_usize()] = eval_revert as _;
	table[Opcode::INVALID.as_usize()] = INVALID.concrete as _;

	table
};

pub static SYMBOLIC_TABLE: DispatchTable<SymWord, SymbolicCalldata, SymByte> = {
	let mut table = [EXTERNAL.symbolic as _; 256];

	table[Opcode::ADD.as_usize()] = ADD.symbolic as _;
	table[Opcode::MUL.as_usize()] = MUL.symbolic as _;
	table[Opcode::SUB.as_usize()] = SUB.symbolic as _;
	table[Opcode::DIV.as_usize()] = DIV.symbolic as _;
	table[Opcode::SDIV.as_usize()] = SDIV.symbolic as _;
	table[Opcode::MOD.as_usize()] = MOD.symbolic as _;
	table[Opcode::SMOD.as_usize()] = SMOD.symbolic as _;
	table[Opcode::ADDMOD.as_usize()] = ADDMOD.symbolic as _;
	table[Opcode::MULMOD.as_usize()] = MULMOD.symbolic as _;
	table[Opcode::SIGNEXTEND.as_usize()] = SIGNEXTEND.symbolic as _;
	table[Opcode::LT.as_usize()] = LT.symbolic as _;
	table[Opcode::GT.as_usize()] = GT.symbolic as _;
	table[Opcode::SLT.as_usize()] = SLT.symbolic as _;
	table[Opcode::SGT.as_usize()] = SGT.symbolic as _;
	table[Opcode::EQ.as_usize()] = EQ.symbolic as _;
	table[Opcode::ISZERO.as_usize()] = ISZERO.symbolic as _;
	table[Opcode::AND.as_usize()] = AND.symbolic as _;
	table[Opcode::OR.as_usize()] = OR.symbolic as _;
	table[Opcode::XOR.as_usize()] = XOR.symbolic as _;
	table[Opcode::NOT.as_usize()] = NOT.symbolic as _;
	table[Opcode::SHL.as_usize()] = SHL.symbolic as _;
	table[Opcode::SHR.as_usize()] = SHR.symbolic as _;
	table[Opcode::SAR.as_usize()] = SAR.symbolic as _;
	table[Opcode::CODESIZE.as_usize()] = CODESIZE.symbolic as _;
	table[Opcode::CODECOPY.as_usize()] = CODECOPY.symbolic as _;
	table[Opcode::CALLDATALOAD.as_usize()] = CALLDATALOAD.symbolic as _;
	table[Opcode::CALLDATASIZE.as_usize()] = CALLDATASIZE.symbolic as _;
	table[Opcode::CALLDATACOPY.as_usize()] = CALLDATACOPY.symbolic as _;
	table[Opcode::POP.as_usize()] = POP.symbolic as _;
	table[Opcode::MLOAD.as_usize()] = MLOAD.symbolic as _;
	table[Opcode::PC.as_usize()] = PC.symbolic as _;

	table[Opcode::DUP1.as_usize()] = DUP1.symbolic as _;
	table[Opcode::DUP2.as_usize()] = DUP2.symbolic as _;
	table[Opcode::DUP3.as_usize()] = DUP3.symbolic as _;
	table[Opcode::DUP4.as_usize()] = DUP4.symbolic as _;
	table[Opcode::DUP5.as_usize()] = DUP5.symbolic as _;
	table[Opcode::DUP6.as_usize()] = DUP6.symbolic as _;
	table[Opcode::DUP7.as_usize()] = DUP7.symbolic as _;
	table[Opcode::DUP8.as_usize()] = DUP8.symbolic as _;
	table[Opcode::DUP9.as_usize()] = DUP9.symbolic as _;
	table[Opcode::DUP10.as_usize()] = DUP10.symbolic as _;
	table[Opcode::DUP11.as_usize()] = DUP11.symbolic as _;
	table[Opcode::DUP12.as_usize()] = DUP12.symbolic as _;
	table[Opcode::DUP13.as_usize()] = DUP13.symbolic as _;
	table[Opcode::DUP14.as_usize()] = DUP14.symbolic as _;
	table[Opcode::DUP15.as_usize()] = DUP15.symbolic as _;
	table[Opcode::DUP16.as_usize()] = DUP16.symbolic as _;

	table[Opcode::SWAP1.as_usize()] = SWAP1.symbolic as _;
	table[Opcode::SWAP2.as_usize()] = SWAP2.symbolic as _;
	table[Opcode::SWAP3.as_usize()] = SWAP3.symbolic as _;
	table[Opcode::SWAP4.as_usize()] = SWAP4.symbolic as _;
	table[Opcode::SWAP5.as_usize()] = SWAP5.symbolic as _;
	table[Opcode::SWAP6.as_usize()] = SWAP6.symbolic as _;
	table[Opcode::SWAP7.as_usize()] = SWAP7.symbolic as _;
	table[Opcode::SWAP8.as_usize()] = SWAP8.symbolic as _;
	table[Opcode::SWAP9.as_usize()] = SWAP9.symbolic as _;
	table[Opcode::SWAP10.as_usize()] = SWAP10.symbolic as _;
	table[Opcode::SWAP11.as_usize()] = SWAP11.symbolic as _;
	table[Opcode::SWAP12.as_usize()] = SWAP12.symbolic as _;
	table[Opcode::SWAP13.as_usize()] = SWAP13.symbolic as _;
	table[Opcode::SWAP14.as_usize()] = SWAP14.symbolic as _;
	table[Opcode::SWAP15.as_usize()] = SWAP15.symbolic as _;
	table[Opcode::SWAP16.as_usize()] = SWAP16.symbolic as _;

	table[Opcode::INVALID.as_usize()] = INVALID.symbolic as _;

	table
};
