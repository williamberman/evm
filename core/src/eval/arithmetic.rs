use super::Control;
use crate::utils::I256;
use core::convert::TryInto;
use core::ops::Rem;
use primitive_types::{U256, U512};

#[inline]
pub fn div(op1: U256, op2: U256) -> U256 {
	if op2 == U256::zero() {
		U256::zero()
	} else {
		op1 / op2
	}
}

#[inline]
pub fn sdiv(op1: U256, op2: U256) -> U256 {
	let op1: I256 = op1.into();
	let op2: I256 = op2.into();
	let ret = op1 / op2;
	ret.into()
}

#[inline]
pub fn rem(op1: U256, op2: U256) -> U256 {
	if op2 == U256::zero() {
		U256::zero()
	} else {
		op1.rem(op2)
	}
}

#[inline]
pub fn srem(op1: U256, op2: U256) -> U256 {
	if op2 == U256::zero() {
		U256::zero()
	} else {
		let op1: I256 = op1.into();
		let op2: I256 = op2.into();
		let ret = op1.rem(op2);
		ret.into()
	}
}

#[inline]
pub fn addmod(op1: U256, op2: U256, op3: U256) -> U256 {
	let op1: U512 = op1.into();
	let op2: U512 = op2.into();
	let op3: U512 = op3.into();

	if op3 == U512::zero() {
		U256::zero()
	} else {
		let v = (op1 + op2) % op3;
		v.try_into()
			.expect("op3 is less than U256::MAX, thus it never overflows; qed")
	}
}

#[inline]
pub fn mulmod(op1: U256, op2: U256, op3: U256) -> U256 {
	let op1: U512 = op1.into();
	let op2: U512 = op2.into();
	let op3: U512 = op3.into();

	if op3 == U512::zero() {
		U256::zero()
	} else {
		let v = (op1 * op2) % op3;
		v.try_into()
			.expect("op3 is less than U256::MAX, thus it never overflows; qed")
	}
}

#[inline]
pub fn exp(op1: U256, op2: U256) -> U256 {
	let mut op1 = op1;
	let mut op2 = op2;
	let mut r: U256 = 1.into();

	while op2 != 0.into() {
		if op2 & 1.into() != 0.into() {
			r = r.overflowing_mul(op1).0;
		}
		op2 >>= 1;
		op1 = op1.overflowing_mul(op1).0;
	}

	r
}

/// In the yellow paper `SIGNEXTEND` is defined to take two inputs, we will call them
/// `x` and `y`, and produce one output. The first `t` bits of the output (numbering from the
/// left, starting from 0) are equal to the `t`-th bit of `y`, where `t` is equal to
/// `256 - 8(x + 1)`. The remaining bits of the output are equal to the corresponding bits of `y`.
/// Note: if `x >= 32` then the output is equal to `y` since `t <= 0`. To efficiently implement
/// this algorithm in the case `x < 32` we do the following. Let `b` be equal to the `t`-th bit
/// of `y` and let `s = 255 - t = 8x + 7` (this is effectively the same index as `t`, but
/// numbering the bits from the right instead of the left). We can create a bit mask which is all
/// zeros up to and including the `t`-th bit, and all ones afterwards by computing the quantity
/// `2^s - 1`. We can use this mask to compute the output depending on the value of `b`.
/// If `b == 1` then the yellow paper says the output should be all ones up to
/// and including the `t`-th bit, followed by the remaining bits of `y`; this is equal to
/// `y | !mask` where `|` is the bitwise `OR` and `!` is bitwise negation. Similarly, if
/// `b == 0` then the yellow paper says the output should start with all zeros, then end with
/// bits from `b`; this is equal to `y & mask` where `&` is bitwise `AND`.
#[inline]
pub fn signextend(op1: U256, op2: U256) -> U256 {
	if op1 < U256::from(32) {
		// `low_u32` works since op1 < 32
		let bit_index = (8 * op1.low_u32() + 7) as usize;
		let bit = op2.bit(bit_index);
		let mask = (U256::one() << bit_index) - U256::one();
		if bit {
			op2 | !mask
		} else {
			op2 & mask
		}
	} else {
		op2
	}
}

pub mod sym {
	use super::Control;
	use crate::{
		symbolic::{bv_256_zero, bv_constant},
		Machine, SymStackItem,
	};
	use amzn_smt_ir::{logic::BvOp, CoreOp, Index, Term};
	use num::bigint::ToBigUint;
	use primitive_types::{H256, H512, U256, U512};
	use smallvec::{smallvec, SmallVec};

	pub fn addmod(state: &mut Machine<SymStackItem>) -> Control {
		modop(state, super::addmod, |a, b| a + b, BvOp::BvAdd)
	}

	pub fn mulmod(state: &mut Machine<SymStackItem>) -> Control {
		modop(state, super::mulmod, |a, b| a * b, BvOp::BvMul)
	}

	pub fn modop(
		state: &mut Machine<SymStackItem>,
		all_concrete_f: fn(U256, U256, U256) -> U256,
		init_op_concrete_f: fn(U512, U512) -> U512,
		bv_op_constructor: fn(SmallVec<[Term; 2]>) -> BvOp<Term>,
	) -> Control {
		pop!(state, op1, op2, op3);

		let ret = all_concrete(op1.clone(), op2.clone(), op3.clone(), all_concrete_f)
			.or_else(|| init_op_concrete(op1.clone(), op2.clone(), op3.clone(), init_op_concrete_f))
			.or_else(|| mod_op_concrete(op1.clone(), op2.clone(), op3.clone(), bv_op_constructor))
			.or_else(|| mod_op(op1.clone(), op2.clone(), op3.clone(), bv_op_constructor))
			.unwrap();

		push!(state, ret);

		Control::Continue(1)
	}

	fn all_concrete(
		op1: SymStackItem,
		op2: SymStackItem,
		op3: SymStackItem,
		f: fn(U256, U256, U256) -> U256,
	) -> Option<SymStackItem> {
		match (op1, op2, op3) {
			// We can perform everything concretely
			(
				SymStackItem::Concrete(op1),
				SymStackItem::Concrete(op2),
				SymStackItem::Concrete(op3),
			) => SymStackItem::Concrete(uth(f(htu(op1), htu(op2), htu(op3)))).into(),
			_ => None,
		}
	}

	// Both of the non-modulus args are concrete
	// We can concretely
	// - perform the initial (non-modulus) operation
	fn init_op_concrete(
		op1: SymStackItem,
		op2: SymStackItem,
		op3: SymStackItem,
		f: fn(U512, U512) -> U512,
	) -> Option<SymStackItem> {
		let (op1, op2, sym3): (U512, U512, Term) = match (op1, op2, op3) {
			(
				SymStackItem::Concrete(xop1),
				SymStackItem::Concrete(xop2),
				SymStackItem::Symbolic(sym3),
			) => (
				htu(xop1).into(),
				htu(xop2).into(),
				symbolic_zero_extend(sym3),
			),

			_ => return None,
		};

		SymStackItem::Symbolic(
			CoreOp::Ite(
				// Check on the modulus
				CoreOp::Eq(smallvec![sym3.clone().into(), bv_256_zero()]).into(),
				bv_256_zero(),
				symbolic_truncate(
					BvOp::BvUrem(bv_constant(uth512(f(op1, op2)).as_bytes().to_vec()), sym3).into(),
				),
			)
			.into(),
		)
		.into()
	}

	// The modulus and 0 or more of the other terms are concrete
	// We can concretely
	// - perform the check if the modulus is 0
	// - zero extend the modulus
	// - zero extend those other arguments which are concrete
	fn mod_op_concrete(
		op1: SymStackItem,
		op2: SymStackItem,
		op3: SymStackItem,
		f: fn(SmallVec<[Term; 2]>) -> BvOp<Term>,
	) -> Option<SymStackItem> {
		let (sym1, sym2, op3) = match (op1, op2, op3) {
			(
				SymStackItem::Symbolic(sym1),
				SymStackItem::Symbolic(sym2),
				SymStackItem::Concrete(xop3),
			) => (symbolic_zero_extend(sym1), symbolic_zero_extend(sym2), xop3),

			(
				SymStackItem::Concrete(xop1),
				SymStackItem::Symbolic(sym2),
				SymStackItem::Concrete(xop3),
			) => (concrete_zero_extend(xop1), symbolic_zero_extend(sym2), xop3),

			(
				SymStackItem::Symbolic(sym1),
				SymStackItem::Concrete(xop2),
				SymStackItem::Concrete(xop3),
			) => (symbolic_zero_extend(sym1), concrete_zero_extend(xop2), xop3),

			_ => return None,
		};

		// Concrete check if modulus is 0
		if op3 == H256::zero() {
			return SymStackItem::Concrete(H256::zero()).into();
		}

		SymStackItem::Symbolic(symbolic_truncate(
			BvOp::BvUrem(
				f(smallvec![sym1.into(), sym2.into()]).into(),
				// Concretely zero extended
				concrete_zero_extend(op3),
			)
			.into(),
		))
		.into()
	}

	// No operation besides zero extention can be done concretely
	fn mod_op(
		op1: SymStackItem,
		op2: SymStackItem,
		op3: SymStackItem,
		f: fn(SmallVec<[Term; 2]>) -> BvOp<Term>,
	) -> Option<SymStackItem> {
		let (sym1, sym2, sym3) = match (op1, op2, op3) {
			(
				SymStackItem::Symbolic(sym1),
				SymStackItem::Symbolic(sym2),
				SymStackItem::Symbolic(sym3),
			) => (
				symbolic_zero_extend(sym1),
				symbolic_zero_extend(sym2),
				symbolic_zero_extend(sym3),
			),

			(
				SymStackItem::Concrete(xop1),
				SymStackItem::Symbolic(sym2),
				SymStackItem::Symbolic(sym3),
			) => (
				concrete_zero_extend(xop1),
				symbolic_zero_extend(sym2),
				symbolic_zero_extend(sym3),
			),

			(
				SymStackItem::Symbolic(sym1),
				SymStackItem::Concrete(xop2),
				SymStackItem::Symbolic(sym3),
			) => (
				symbolic_zero_extend(sym1),
				concrete_zero_extend(xop2),
				symbolic_zero_extend(sym3),
			),

			_ => return None,
		};

		SymStackItem::Symbolic(
			CoreOp::Ite(
				// Check on the modulus
				CoreOp::Eq(smallvec![sym3.clone().into(), bv_256_zero()]).into(),
				bv_256_zero(),
				symbolic_truncate(
					BvOp::BvUrem(
						// Perform the arithmetic operation
						f(smallvec![sym1, sym2]).into(),
						sym3,
					)
					.into(),
				),
			)
			.into(),
		)
		.into()
	}

	fn htu(h: H256) -> U256 {
		U256::from_big_endian(&h[..])
	}

	fn uth(u: U256) -> H256 {
		let mut rv = H256::default();
		u.to_big_endian(&mut rv[..]);
		rv
	}

	fn uth512<T: Into<U512>>(u: T) -> H512 {
		let uu: U512 = u.into();
		let mut rv = H512::default();
		uu.to_big_endian(&mut rv[..]);
		rv
	}

	// Zero extend BitVec(256) to BitVec(512)
	//
	// Note this doesn't provide any checks on sorts of given terms and
	// blindly zero extends by 256 bits
	fn symbolic_zero_extend(sym: Term) -> Term {
		BvOp::ZeroExtend([Index::Numeral(256_i32.to_biguint().unwrap()).into()], sym).into()
	}

	// Zero extend the concrete value and return it as a
	// (constant) symbolic BitVec(512)
	fn concrete_zero_extend(op: H256) -> Term {
		bv_constant(uth512(htu(op)).as_bytes().to_vec())
	}

	// BitVec(512) -> BitVec(256)
	//
	// Note this doesn't provide any checks on sorts of given terms and
	// blindly extracts the lower 256 bits
	fn symbolic_truncate(t: Term) -> Term {
		BvOp::Extract(
			[
				Index::Numeral(255_i32.to_biguint().unwrap()).into(),
				Index::Numeral(0_i32.to_biguint().unwrap()).into(),
			],
			t,
		)
		.into()
	}
}

#[cfg(test)]
mod tests {
	use super::{signextend, U256};

	/// Test to ensure new (optimized) `signextend` implementation is equivalent to the previous
	/// implementation.
	#[test]
	fn test_signextend() {
		let test_values = vec![
			U256::zero(),
			U256::one(),
			U256::from(8),
			U256::from(10),
			U256::from(65),
			U256::from(100),
			U256::from(128),
			U256::from(11) * (U256::one() << 65),
			U256::from(7) * (U256::one() << 123),
			U256::MAX / 167,
			U256::MAX,
		];
		for x in 0..64 {
			for y in test_values.iter() {
				compare_old_signextend(x.into(), *y);
			}
		}
	}

	fn compare_old_signextend(x: U256, y: U256) {
		let old = old_signextend(x, y);
		let new = signextend(x, y);

		assert_eq!(old, new);
	}

	fn old_signextend(op1: U256, op2: U256) -> U256 {
		if op1 > U256::from(32) {
			op2
		} else {
			let mut ret = U256::zero();
			let len: usize = op1.as_usize();
			let t: usize = 8 * (len + 1) - 1;
			let t_bit_mask = U256::one() << t;
			let t_value = (op2 & t_bit_mask) >> t;
			for i in 0..256 {
				let bit_mask = U256::one() << i;
				let i_value = (op2 & bit_mask) >> i;
				if i <= t {
					ret = ret.overflowing_add(i_value << i).0;
				} else {
					ret = ret.overflowing_add(t_value << i).0;
				}
			}
			ret
		}
	}
}
