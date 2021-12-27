#[macro_use]
mod macros;
mod arithmetic;
mod bitwise;
mod misc;

use crate::{
	stack::{StackItem, SymStackItem},
	symbolic::{self, bv_constant},
	ExitError, ExitReason, ExitSucceed, Machine, Opcode,
};
use amzn_smt_ir::{
	logic::{BvOp},
	CoreOp, Index,
};
use core::ops::{BitAnd, BitOr, BitXor};
use num::bigint::ToBigUint;
use primitive_types::{H256, U256};
use smallvec::smallvec;

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Control {
	Continue(usize),
	Exit(ExitReason),
	Jump(usize),
	Trap(Opcode),
}

type OpEval<T> = fn(state: &mut Machine<T>, opcode: Opcode, position: usize) -> Control;

struct OpEvals {
	concrete: OpEval<H256>,
	symbolic: OpEval<SymStackItem>,
}

fn eval_stop<T: StackItem>(_state: &mut Machine<T>, _opcode: Opcode, _position: usize) -> Control {
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
	concrete: |state: &mut Machine<H256>, _opcode: Opcode, _position: usize| -> Control {
		op3_u256_fn!(state, self::arithmetic::addmod)
	},

	symbolic: |state: &mut Machine<SymStackItem>, _opcode: Opcode, _position: usize| -> Control {
		arithmetic::sym::addmod(state)
	},
};

static MULMOD: OpEvals = OpEvals {
	concrete: |state: &mut Machine<H256>, _opcode: Opcode, _position: usize| -> Control {
		op3_u256_fn!(state, self::arithmetic::mulmod)
	},

	symbolic: |state: &mut Machine<SymStackItem>, _opcode: Opcode, _position: usize| -> Control {
		arithmetic::sym::mulmod(state)
	},
};

fn eval_exp(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	op2_u256_fn!(state, self::arithmetic::exp)
}

static SIGNEXTEND: OpEvals = OpEvals {
	concrete: |state: &mut Machine<H256>, _opcode: Opcode, _position: usize| -> Control {
		op2_u256_fn!(state, self::arithmetic::signextend)
	},
	symbolic: |state: &mut Machine<SymStackItem>, _opcode: Opcode, _position: usize| -> Control {
		pop!(state, op1, op2);

		let ret = match (op1, op2) {
			(SymStackItem::Concrete(xop1), SymStackItem::Concrete(xop2)) => {
				let xxop1 = U256::from_big_endian(&xop1[..]);
				let xxop2 = U256::from_big_endian(&xop2[..]);

				let v = self::arithmetic::signextend(xxop1, xxop2);

				let mut xv = H256::default();

				v.to_big_endian(&mut xv[..]);

				SymStackItem::Concrete(xv)
			}

			// We are sign extending the second argument by the first argument
			(SymStackItem::Concrete(xop1), SymStackItem::Symbolic(sym2)) => {
				let n = U256::from_big_endian(&xop1[..])
					.as_u64()
					.to_biguint()
					.unwrap();
				SymStackItem::Symbolic(BvOp::SignExtend([Index::Numeral(n).into()], sym2).into())
			}

			(SymStackItem::Symbolic(_sym1), SymStackItem::Concrete(_xop2)) => {
				panic!("Cannot sign extend by a symbolic value")
			}

			(SymStackItem::Symbolic(_sym1), SymStackItem::Symbolic(_sym2)) => {
				panic!("Cannot sign extend by a symbolic value")
			}
		};

		push!(state, ret);

		Control::Continue(1)
	},
};

op2_evals_bool_tuple!(LT, lt, BvOp::BvUlt);
op2_evals_bool_tuple!(GT, gt, BvOp::BvUgt);
op2_evals_bool_fn!(SLT, self::bitwise::slt, BvOp::BvSlt);
op2_evals_bool_fn!(SGT, self::bitwise::sgt, BvOp::BvSgt);
op2_evals_bool_tuple_vec!(EQ, eq, CoreOp::Eq);

fn eval_iszero(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	op1_u256_fn!(state, self::bitwise::iszero)
}

fn eval_and(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	op2_u256!(state, bitand)
}

fn eval_or(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	op2_u256!(state, bitor)
}

fn eval_xor(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	op2_u256!(state, bitxor)
}

fn eval_not(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	op1_u256_fn!(state, self::bitwise::not)
}

fn eval_byte(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	op2_u256_fn!(state, self::bitwise::byte)
}

fn eval_shl(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	op2_u256_fn!(state, self::bitwise::shl)
}

fn eval_shr(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	op2_u256_fn!(state, self::bitwise::shr)
}

fn eval_sar(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	op2_u256_fn!(state, self::bitwise::sar)
}

fn eval_codesize(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::codesize(state)
}

fn eval_codecopy(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::codecopy(state)
}

fn eval_calldataload(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::calldataload(state)
}

fn eval_calldatasize(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::calldatasize(state)
}

fn eval_calldatacopy(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::calldatacopy(state)
}

fn eval_pop(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::pop(state)
}

fn eval_mload(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::mload(state)
}

fn eval_mstore(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::mstore(state)
}

fn eval_mstore8(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::mstore8(state)
}

fn eval_jump(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::jump(state)
}

fn eval_jumpi(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::jumpi(state)
}

fn eval_pc(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::pc(state, position)
}

fn eval_msize(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::msize(state)
}

fn eval_jumpdest<T: StackItem>(
	_state: &mut Machine<T>,
	_opcode: Opcode,
	_position: usize,
) -> Control {
	Control::Continue(1)
}

fn eval_push1(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 1, position)
}

fn eval_push2(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 2, position)
}

fn eval_push3(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 3, position)
}

fn eval_push4(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 4, position)
}

fn eval_push5(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 5, position)
}

fn eval_push6(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 6, position)
}

fn eval_push7(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 7, position)
}

fn eval_push8(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 8, position)
}

fn eval_push9(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 9, position)
}

fn eval_push10(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 10, position)
}

fn eval_push11(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 11, position)
}

fn eval_push12(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 12, position)
}

fn eval_push13(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 13, position)
}

fn eval_push14(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 14, position)
}

fn eval_push15(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 15, position)
}

fn eval_push16(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 16, position)
}

fn eval_push17(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 17, position)
}

fn eval_push18(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 18, position)
}

fn eval_push19(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 19, position)
}

fn eval_push20(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 20, position)
}

fn eval_push21(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 21, position)
}

fn eval_push22(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 22, position)
}

fn eval_push23(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 23, position)
}

fn eval_push24(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 24, position)
}

fn eval_push25(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 25, position)
}

fn eval_push26(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 26, position)
}

fn eval_push27(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 27, position)
}

fn eval_push28(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 28, position)
}

fn eval_push29(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 29, position)
}

fn eval_push30(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 30, position)
}

fn eval_push31(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 31, position)
}

fn eval_push32(state: &mut Machine<H256>, _opcode: Opcode, position: usize) -> Control {
	self::misc::push(state, 32, position)
}

fn eval_dup1(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::dup(state, 1)
}

fn eval_dup2(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::dup(state, 2)
}

fn eval_dup3(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::dup(state, 3)
}

fn eval_dup4(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::dup(state, 4)
}

fn eval_dup5(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::dup(state, 5)
}

fn eval_dup6(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::dup(state, 6)
}

fn eval_dup7(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::dup(state, 7)
}

fn eval_dup8(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::dup(state, 8)
}

fn eval_dup9(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::dup(state, 9)
}

fn eval_dup10(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::dup(state, 10)
}

fn eval_dup11(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::dup(state, 11)
}

fn eval_dup12(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::dup(state, 12)
}

fn eval_dup13(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::dup(state, 13)
}

fn eval_dup14(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::dup(state, 14)
}

fn eval_dup15(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::dup(state, 15)
}

fn eval_dup16(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::dup(state, 16)
}

fn eval_swap1(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::swap(state, 1)
}

fn eval_swap2(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::swap(state, 2)
}

fn eval_swap3(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::swap(state, 3)
}

fn eval_swap4(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::swap(state, 4)
}

fn eval_swap5(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::swap(state, 5)
}

fn eval_swap6(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::swap(state, 6)
}

fn eval_swap7(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::swap(state, 7)
}

fn eval_swap8(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::swap(state, 8)
}

fn eval_swap9(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::swap(state, 9)
}

fn eval_swap10(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::swap(state, 10)
}

fn eval_swap11(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::swap(state, 11)
}

fn eval_swap12(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::swap(state, 12)
}

fn eval_swap13(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::swap(state, 13)
}

fn eval_swap14(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::swap(state, 14)
}

fn eval_swap15(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::swap(state, 15)
}

fn eval_swap16(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::swap(state, 16)
}

fn eval_return(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::ret(state)
}

fn eval_revert(state: &mut Machine<H256>, _opcode: Opcode, _position: usize) -> Control {
	self::misc::revert(state)
}

fn eval_invalid<T: StackItem>(
	_state: &mut Machine<T>,
	_opcode: Opcode,
	_position: usize,
) -> Control {
	Control::Exit(ExitError::DesignatedInvalid.into())
}

fn eval_external<T: StackItem>(
	_state: &mut Machine<T>,
	opcode: Opcode,
	_position: usize,
) -> Control {
	Control::Trap(opcode)
}

pub type DispatchTable<T> =
	[fn(state: &mut Machine<T>, opcode: Opcode, position: usize) -> Control; 256];

pub static CONCRETE_TABLE: DispatchTable<H256> = {
	let mut table = [eval_external as _; 256];

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
	table[Opcode::ISZERO.as_usize()] = eval_iszero as _;
	table[Opcode::AND.as_usize()] = eval_and as _;
	table[Opcode::OR.as_usize()] = eval_or as _;
	table[Opcode::XOR.as_usize()] = eval_xor as _;
	table[Opcode::NOT.as_usize()] = eval_not as _;
	table[Opcode::BYTE.as_usize()] = eval_byte as _;
	table[Opcode::SHL.as_usize()] = eval_shl as _;
	table[Opcode::SHR.as_usize()] = eval_shr as _;
	table[Opcode::SAR.as_usize()] = eval_sar as _;
	table[Opcode::CODESIZE.as_usize()] = eval_codesize as _;
	table[Opcode::CODECOPY.as_usize()] = eval_codecopy as _;
	table[Opcode::CALLDATALOAD.as_usize()] = eval_calldataload as _;
	table[Opcode::CALLDATASIZE.as_usize()] = eval_calldatasize as _;
	table[Opcode::CALLDATACOPY.as_usize()] = eval_calldatacopy as _;
	table[Opcode::POP.as_usize()] = eval_pop as _;
	table[Opcode::MLOAD.as_usize()] = eval_mload as _;
	table[Opcode::MSTORE.as_usize()] = eval_mstore as _;
	table[Opcode::MSTORE8.as_usize()] = eval_mstore8 as _;
	table[Opcode::JUMP.as_usize()] = eval_jump as _;
	table[Opcode::JUMPI.as_usize()] = eval_jumpi as _;
	table[Opcode::PC.as_usize()] = eval_pc as _;
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

	table[Opcode::DUP1.as_usize()] = eval_dup1 as _;
	table[Opcode::DUP2.as_usize()] = eval_dup2 as _;
	table[Opcode::DUP3.as_usize()] = eval_dup3 as _;
	table[Opcode::DUP4.as_usize()] = eval_dup4 as _;
	table[Opcode::DUP5.as_usize()] = eval_dup5 as _;
	table[Opcode::DUP6.as_usize()] = eval_dup6 as _;
	table[Opcode::DUP7.as_usize()] = eval_dup7 as _;
	table[Opcode::DUP8.as_usize()] = eval_dup8 as _;
	table[Opcode::DUP9.as_usize()] = eval_dup9 as _;
	table[Opcode::DUP10.as_usize()] = eval_dup10 as _;
	table[Opcode::DUP11.as_usize()] = eval_dup11 as _;
	table[Opcode::DUP12.as_usize()] = eval_dup12 as _;
	table[Opcode::DUP13.as_usize()] = eval_dup13 as _;
	table[Opcode::DUP14.as_usize()] = eval_dup14 as _;
	table[Opcode::DUP15.as_usize()] = eval_dup15 as _;
	table[Opcode::DUP16.as_usize()] = eval_dup16 as _;

	table[Opcode::SWAP1.as_usize()] = eval_swap1 as _;
	table[Opcode::SWAP2.as_usize()] = eval_swap2 as _;
	table[Opcode::SWAP3.as_usize()] = eval_swap3 as _;
	table[Opcode::SWAP4.as_usize()] = eval_swap4 as _;
	table[Opcode::SWAP5.as_usize()] = eval_swap5 as _;
	table[Opcode::SWAP6.as_usize()] = eval_swap6 as _;
	table[Opcode::SWAP7.as_usize()] = eval_swap7 as _;
	table[Opcode::SWAP8.as_usize()] = eval_swap8 as _;
	table[Opcode::SWAP9.as_usize()] = eval_swap9 as _;
	table[Opcode::SWAP10.as_usize()] = eval_swap10 as _;
	table[Opcode::SWAP11.as_usize()] = eval_swap11 as _;
	table[Opcode::SWAP12.as_usize()] = eval_swap12 as _;
	table[Opcode::SWAP13.as_usize()] = eval_swap13 as _;
	table[Opcode::SWAP14.as_usize()] = eval_swap14 as _;
	table[Opcode::SWAP15.as_usize()] = eval_swap15 as _;
	table[Opcode::SWAP16.as_usize()] = eval_swap16 as _;

	table[Opcode::RETURN.as_usize()] = eval_return as _;
	table[Opcode::REVERT.as_usize()] = eval_revert as _;
	table[Opcode::INVALID.as_usize()] = eval_invalid as _;

	table
};

pub static SYMBOLIC_TABLE: DispatchTable<SymStackItem> = {
	let mut table = [eval_external as _; 256];

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

	table
};
