use crate::symbolic::{bv_constant_from_u256, bv_8_n, SymWord, bv_256_n};
pub use crate::valids::Valids;

use crate::eval::{htu};
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
pub struct SymbolicCalldata {
	n_bytes: SymWord,
	elements: Vec<(U256, u8)>,
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
	pub fn load(&self, index: SymWord) -> SymWord {
		match index {
			SymWord::Concrete(index) => self.load_from_concrete_index(&index),

			SymWord::Symbolic(index) => self.load_from_symbolic_index(&index),
		}
	}

	fn get(&self, index: &U256) -> Option<u8> {
		self.elements.iter().find(|x| x.0 == *index)?.1.into()
	}

	fn load_from_symbolic_index(&self, index: &Term) -> SymWord {
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

	fn load_from_concrete_index(&self, index: &H256) -> SymWord {
		let mut all_concrete = true;

		enum AtIndex {
			Concrete(u8),
			Symbolic(Term),
		}

		let mut values = Vec::with_capacity(32);

		for offset in 0..=31 {
			// A value is concrete if

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
						Some(n) => AtIndex::Concrete(n),

						// Check if there is already a known concrete value at this byte
						None => match self.get(&index) {
							Some(n) => AtIndex::Concrete(n),

							None => {
								all_concrete = false;

								AtIndex::Symbolic(Term::UF(
									UF {
										func: CALLDATA_FUNC_NAME.into(),
										args: Box::new([bv_constant_from_u256(&index)]),
									}
									.into(),
								))
							}
						},
					}
				}

				None => {
					// index overflow
					AtIndex::Concrete(0)
				}
			};

			values[offset] = n;
		}

		if all_concrete {
			let mut bytes = [0_u8; 32];

			for (i, x) in values.iter().enumerate() {
				if i >= 32 {
					panic!("not reachable")
				}

				let x = match x {
					&AtIndex::Concrete(x) => x,
					_ => panic!("not reachable"),
				};

				bytes[i] = x;
			}

			SymWord::Concrete(H256::from(bytes))
		} else {
			let mut term: Option<Term> = None;

			for x in values.into_iter() {
				let xterm = match x {
					AtIndex::Concrete(n) => bv_8_n(n),
					AtIndex::Symbolic(t) => t,
				};

				term = Some(match term {
					Some(t) => BvOp::Concat(t, xterm).into(),
					None => xterm
				});
			}

			SymWord::Symbolic(term.unwrap())
		}
	}
}
