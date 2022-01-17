use crate::symbolic::{bv_256_n, bv_8_n, bv_constant_from_u256, SymByte, SymWord};
pub use crate::valids::Valids;

use crate::eval::{htu, uth};
use alloc::vec::Vec;
use amzn_smt_ir::logic::BvOp;
use amzn_smt_ir::{Term, UF};
use primitive_types::{H256, U256};

use smallvec::smallvec;

/// The calldata is modeled as an uninterpreted function
/// of words to bytes. I.e.
/// `(declare-fun calldata ((_ BitVec 256)) (_ BitVec 8))`
///
/// Reading beyond the end of calldata should return #x00 for each byte beyond. This
/// is enforced with an additional universal quantifier. I.e.
/// ```smtlib
/// (declare-const n-calldata-bytes (_ BitVec 256))
/// (assert (forall ((x (_ BitVec 256))) (=> (bvuge x n-calldata-bytes) (= (calldata x) #x00))))
/// ```
#[derive(Clone)]
pub struct SymbolicCalldata {
	pub n_bytes: SymWord,
	pub elements: Vec<(U256, u8)>,
}

impl From<Vec<u8>> for SymbolicCalldata {
	fn from(bytes: Vec<u8>) -> Self {
		let n_bytes = SymWord::Concrete(uth(&U256::from(bytes.len())));
		let elements = bytes
			.into_iter()
			.enumerate()
			.map(|(idx, b)| (U256::from(idx), b))
			.collect();

		Self { n_bytes, elements }
	}
}

impl Default for SymbolicCalldata {
	fn default() -> Self {
		Self {
			n_bytes: SymWord::Concrete(H256::zero()),
			elements: Default::default(),
		}
	}
}

static CALLDATA_FUNC_NAME: &str = "calldata";

impl SymbolicCalldata {
	pub fn from_function_selector(sel: Vec<u8>, arg_length: usize) -> Self {
		let n_bytes = SymWord::Concrete(uth(&U256::from(sel.len() * 8 + arg_length)));
		let elements = sel
			.into_iter()
			.enumerate()
			.map(|(idx, b)| (U256::from(idx), b))
			.collect();

		return Self { n_bytes, elements };
	}

	pub fn load(&self, index: SymWord) -> SymWord {
		match index {
			SymWord::Concrete(index) => self.load_from_concrete_index(&index),

			SymWord::Symbolic(index) => self.load_from_symbolic_index(&index),
		}
	}

	pub fn get(&self, index: &U256) -> SymByte {
		let n = self.elements.iter().find(|x| x.0 == *index);

		match n {
			Some(n) => SymByte::Concrete(n.1),
			None => SymByte::Symbolic(Term::UF(
				UF {
					func: CALLDATA_FUNC_NAME.into(),
					args: Box::new([bv_constant_from_u256(&index)]),
				}
				.into(),
			)),
		}
	}

	pub fn get_byte(&self, index: usize) -> u8 {
		let index = U256::from(index);
		let n = self.elements.iter().find(|x| x.0 == index);
		n.unwrap().1
	}

	pub fn load_from_symbolic_index(&self, index: &Term) -> SymWord {
		// First byte
		let mut term: Term = Term::UF(
			UF {
				func: CALLDATA_FUNC_NAME.into(),
				args: Box::new([index.clone()]),
			}
			.into(),
		);

		// Read the 31 remaining bytes to complete the word
		for offset in 1..=31 {
			term = BvOp::Concat(
				term,
				Term::UF(
					UF {
						func: CALLDATA_FUNC_NAME.into(),
						args: Box::new([
							BvOp::BvAdd(smallvec![index.clone(), bv_256_n(offset)]).into()
						]),
					}
					.into(),
				),
			)
			.into()
		}

		SymWord::Symbolic(term)
	}

	pub fn load_from_concrete_index(&self, index: &H256) -> SymWord {
		let mut all_concrete = true;

		let mut values = Vec::with_capacity(32);

		for offset in 0..=31 {
			let index = htu(index).checked_add(U256::from(offset));

			let n = match index {
				Some(index) => {
					// Check if reading beyond end of calldata
					let rv = if let SymWord::Concrete(n_bytes) = self.n_bytes {
						if index.ge(&htu(&n_bytes)) {
							Some(0)
						} else {
							None
						}
					} else {
						None
					};

					match rv {
						Some(n) => SymByte::Concrete(n),

						// Check if there is already a known concrete value at this byte
						None => {
							let n = self.get(&index);

							if let SymByte::Symbolic(_) = n {
								all_concrete = false;
							}

							n
						}
					}
				}

				None => {
					// index overflow
					SymByte::Concrete(0)
				}
			};

			values.push(n);
		}

		if all_concrete {
			let mut bytes = [0_u8; 32];

			for (i, x) in values.iter().enumerate() {
				if i >= 32 {
					panic!("not reachable")
				}

				let x = match x {
					&SymByte::Concrete(x) => x,
					_ => panic!("not reachable"),
				};

				bytes[i] = x;
			}

			SymWord::Concrete(H256::from(bytes))
		} else {
			let mut term: Option<Term> = None;

			for x in values.into_iter() {
				let xterm = match x {
					SymByte::Concrete(n) => bv_8_n(n),
					SymByte::Symbolic(t) => t,
				};

				term = Some(match term {
					Some(t) => BvOp::Concat(t, xterm).into(),
					None => xterm,
				});
			}

			SymWord::Symbolic(term.unwrap())
		}
	}
}
