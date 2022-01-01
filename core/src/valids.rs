use crate::{symbolic::SymByte, Opcode};
use alloc::vec::Vec;

/// Mapping of valid jump destination from code.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Valids(Vec<bool>);

impl Valids {
	/// Get the length of the valid mapping. This is the same as the
	/// code bytes.
	#[inline]
	pub fn len(&self) -> usize {
		self.0.len()
	}

	/// Returns true if the valids list is empty
	#[inline]
	pub fn is_empty(&self) -> bool {
		self.len() == 0
	}

	/// Returns `true` if the position is a valid jump destination. If
	/// not, returns `false`.
	pub fn is_valid(&self, position: usize) -> bool {
		if position >= self.0.len() {
			return false;
		}

		if !self.0[position] {
			return false;
		}

		true
	}
}

impl From<&[u8]> for Valids {
	/// Create a new valid mapping from given code bytes.
	fn from(code: &[u8]) -> Self {
		let mut valids: Vec<bool> = Vec::with_capacity(code.len());
		valids.resize(code.len(), false);

		let mut i = 0;
		while i < code.len() {
			let opcode = Opcode(code[i]);
			let (is_valid, inc) = check_opcode(opcode);
			valids[i] = is_valid;
			i += inc;
		}

		Valids(valids)
	}
}

impl From<&[SymByte]> for Valids {
	/// Create a new valid mapping from given code bytes.
	fn from(code: &[SymByte]) -> Self {
		let mut valids: Vec<bool> = Vec::with_capacity(code.len());
		valids.resize(code.len(), false);

		let mut i = 0;
		while i < code.len() {
			if let SymByte::Concrete(byte) = code[i] {
				let opcode = Opcode(byte);
				let (is_valid, inc) = check_opcode(opcode);
				valids[i] = is_valid;
				i += inc;
			}
		}

		Valids(valids)
	}
}

fn check_opcode(opcode: Opcode) -> (bool, usize) {
	if opcode == Opcode::JUMPDEST {
		(true, 1)
	} else if let Some(v) = opcode.is_push() {
		(false, v as usize + 1)
	} else {
		(false, 1)
	}
}
