use crate::utils::{Sign, I256};
use primitive_types::U256;

#[inline]
pub fn slt(op1: U256, op2: U256) -> U256 {
	let op1: I256 = op1.into();
	let op2: I256 = op2.into();

	if op1.lt(&op2) {
		U256::one()
	} else {
		U256::zero()
	}
}

#[inline]
pub fn sgt(op1: U256, op2: U256) -> U256 {
	let op1: I256 = op1.into();
	let op2: I256 = op2.into();

	if op1.gt(&op2) {
		U256::one()
	} else {
		U256::zero()
	}
}

#[inline]
pub fn iszero(op1: U256) -> U256 {
	if op1 == U256::zero() {
		U256::one()
	} else {
		U256::zero()
	}
}

#[inline]
pub fn not(op1: U256) -> U256 {
	!op1
}

#[inline]
pub fn byte(op1: U256, op2: U256) -> U256 {
	let mut ret = U256::zero();

	for i in 0..256 {
		if i < 8 && op1 < 32.into() {
			let o: usize = op1.as_usize();
			let t = 255 - (7 - i + 8 * o);
			let bit_mask = U256::one() << t;
			let value = (op2 & bit_mask) >> t;
			ret = ret.overflowing_add(value << i).0;
		}
	}

	ret
}

#[inline]
pub fn shl(shift: U256, value: U256) -> U256 {
	if value == U256::zero() || shift >= U256::from(256) {
		U256::zero()
	} else {
		let shift: u64 = shift.as_u64();
		value << shift as usize
	}
}

#[inline]
pub fn shr(shift: U256, value: U256) -> U256 {
	if value == U256::zero() || shift >= U256::from(256) {
		U256::zero()
	} else {
		let shift: u64 = shift.as_u64();
		value >> shift as usize
	}
}

#[inline]
pub fn sar(shift: U256, value: U256) -> U256 {
	let value = I256::from(value);

	if value == I256::zero() || shift >= U256::from(256) {
		let I256(sign, _) = value;
		match sign {
			// value is 0 or >=1, pushing 0
			Sign::Plus | Sign::Zero => U256::zero(),
			// value is <0, pushing -1
			Sign::Minus => I256(Sign::Minus, U256::one()).into(),
		}
	} else {
		let shift: u64 = shift.as_u64();

		match value.0 {
			Sign::Plus | Sign::Zero => value.1 >> shift as usize,
			Sign::Minus => {
				let shifted = ((value.1.overflowing_sub(U256::one()).0) >> shift as usize)
					.overflowing_add(U256::one())
					.0;
				I256(Sign::Minus, shifted).into()
			}
		}
	}
}

pub mod sym {
	use amzn_smt_ir::{logic::BvOp, CoreOp, Index, Term};
	use num::bigint::ToBigUint;
	use primitive_types::H256;

	use crate::{
		eval::{htu, uth, Control},
		symbolic::{bv_256_one, bv_256_zero, SymWord},
		SymbolicMachine,
	};

	use smallvec::smallvec;

	pub fn iszero(state: &mut SymbolicMachine) -> Control {
		pop!(state, op);

		let ret = match op {
			SymWord::Concrete(xop) => SymWord::Concrete(uth(&super::iszero(htu(&xop)))),

			SymWord::Symbolic(xop) => SymWord::Symbolic(
				CoreOp::Ite(
					CoreOp::Eq(smallvec![xop, bv_256_zero()]).into(),
					bv_256_one(),
					bv_256_zero(),
				)
				.into(),
			),
		};

		push!(state, ret);

		Control::Continue(1)
	}

	pub fn not(state: &mut SymbolicMachine) -> Control {
		pop!(state, op);

		let ret = match op {
			SymWord::Concrete(xop) => SymWord::Concrete(uth(&super::not(htu(&xop)))),

			SymWord::Symbolic(xop) => SymWord::Symbolic(BvOp::BvNot(xop).into()),
		};

		push!(state, ret);

		Control::Continue(1)
	}

	pub fn byte(state: &mut SymbolicMachine) -> Control {
		// Select byte at index from value. Index starts from high byte
		pop!(state, index, value);

		let index = match index {
			SymWord::Concrete(index) => htu(&index),
			SymWord::Symbolic(_) => panic!("cannot use symbolic index for BYTE"),
		};

		let ret = match value {
			SymWord::Concrete(value) => SymWord::Concrete(uth(&super::byte(index, htu(&value)))),
			SymWord::Symbolic(value) => {
				let index = index.as_usize();

				if index >= 32 {
					SymWord::Concrete(H256::zero())
				} else {
					let low_bit_index = (31 - index) * 31;
					let high_bit_index = low_bit_index + 7;

					SymWord::Symbolic(
						BvOp::ZeroExtend(
							[Index::Numeral(248.to_biguint().unwrap().into()).into()],
							BvOp::Extract(
								[
									Index::Numeral(high_bit_index.to_biguint().unwrap().into()).into(),
									Index::Numeral(low_bit_index.to_biguint().unwrap().into()).into(),
								],
								value,
							)
							.into(),
						)
						.into(),
					)
				}
			}
		};

		push!(state, ret);

		Control::Continue(1)
	}

	pub fn shl(op1: Term, op2: Term) -> Term {
		// Args flipped on purpose
		BvOp::BvShl(op2, op1).into()
	}

	pub fn shr(op1: Term, op2: Term) -> Term {
		BvOp::BvLshr(op2, op1).into()
	}

	pub fn sar(op1: Term, op2: Term) -> Term {
		BvOp::BvAshr(op2, op1).into()
	}
}
