use crate::eval::htu;
use crate::symbolic::{bv_8_n, bv_constant_from_u256, SymByte, SymWord};
use crate::symbolic_calldata::SymbolicCalldata;
use crate::{ExitError, ExitFatal};
use alloc::vec::Vec;
use amzn_smt_ir::logic::BvOp;
use amzn_smt_ir::CoreOp;
use core::cmp::min;
use core::ops::{BitAnd, Not};
use primitive_types::U256;
use std::ops::Add;

pub trait MemoryItem: Clone {}
impl<T: Clone> MemoryItem for T {}

/// A sequencial memory. It uses Rust's `Vec` for internal
/// representation.
#[derive(Clone, Debug)]
pub struct Memory<IMemoryItem: MemoryItem> {
	data: Vec<IMemoryItem>,
	effective_len: U256,
	limit: usize,
	pub default_value: IMemoryItem,
}

pub type ConcreteMemory = Memory<u8>;
pub type SymbolicMemory = Memory<SymByte>;

impl ConcreteMemory {
	pub fn new(limit: usize) -> Self {
		Self::internal_new(limit, 0)
	}
}

impl SymbolicMemory {
	pub fn new(limit: usize) -> Self {
		Self::internal_new(limit, SymByte::Concrete(0))
	}

	pub fn copy_large_symbolic(
		&mut self,
		memory_offset: U256,
		data_offset: U256,
		len: U256,
		data: &SymbolicCalldata,
	) -> Result<(), ExitFatal> {
		if len.is_zero() {
			return Ok(());
		}

		let memory_offset = if memory_offset > U256::from(usize::MAX) {
			return Err(ExitFatal::NotSupported);
		} else {
			memory_offset.as_usize()
		};

		let ulen = if len > U256::from(usize::MAX) {
			return Err(ExitFatal::NotSupported);
		} else {
			len.as_usize()
		};

		let end = match data_offset.checked_add(len) {
			Some(end) => end,
			None => return Ok(()),
		};

		if end > U256::from(usize::MAX) {
			return Ok(());
		}

		let data_offset = data_offset.as_usize();
		let end = end.as_usize();

		let data = match &data.n_bytes {
			SymWord::Concrete(data_len) => {
				let data_len = htu(&data_len);
				if data_len > U256::from(usize::MAX) {
					panic!("concrete calldata length too large.")
				}
				let data_len = data_len.as_usize();

				if data_offset > data_len {
					return Ok(());
				}

				let end = min(end, data_len);
				let mut ns = Vec::with_capacity(end - data_offset);

				let mut idx = data_offset;
				while idx.lt(&end) {
					let n = data.get(&U256::from(idx));
					ns.push(n.clone());
					idx = idx.add(1);
				}

				ns
			}

			SymWord::Symbolic(data_len) => {
				// Perform the length check symbolically
				let mut ns = Vec::with_capacity(ulen);

				for offset in 0..ulen {
					let data_idx = data_offset + offset;
					let memory_idx = memory_offset + offset;

					let data_idx_u256 = U256::from(data_idx);
					let n = match data.get(&data_idx_u256) {
						SymByte::Concrete(n) => bv_8_n(n),
						SymByte::Symbolic(t) => t,
					};

					let mem_val = if memory_idx < self.data.len() {
						self.data[memory_idx].clone()
					} else {
						self.default_value.clone()
					};

					let mem_val = match mem_val {
						crate::symbolic::Sym::Concrete(n) => bv_8_n(n),
						crate::symbolic::Sym::Symbolic(t) => t,
					};


					// Why we have to wrap each byte in a length check
					//
					// When data_offset + len goes beyond the end of the calldata buffer,
					//
					// Note that the diagram shows writing into the memory buffer at the
					// same offset as reading from the memory buffer. This doesn't change
					// the example or what we have to do but remember there's a separate
					// memory write offset.
					//
					//       Calldata buffer
					// 0                        data_len
					// |--------------------------|
					//                     |                  |
					//                     data_offset       len
					//
					//                   Concrete copied
					//                     |------|
					//
					//                      Naive symbolic copy
					//                     |------------------|
					//
					//
					//                   Memory buffer
					// 0                                            memory_len
					// |----------------------------------------------|
					//
					//
					//
					// When `data_len` is concrete, we can ahead of time shrink the copied over buffer.
					//
					// Because we model calldata as a UF that when read beyond the end of its length returns
					// the 0 byte, the naive symbolic copy would write 0 bytes into memory.
					//
					// Instead, we use a conditional to
					// - write the byte from calldata if the calldata index is in calldata's range
					// - write the byte already in memory if the calldata index is out of range
					let op= CoreOp::Ite(
						BvOp::BvUlt(bv_constant_from_u256(&data_idx_u256), data_len.clone()).into(),
						// We are in range, can write the value read from calldata
						n,
						// We are out of range. Must write the existing value in memory at the memory index
						mem_val
					);

					ns.push(SymByte::Symbolic(op.into()));
				}

				ns
			}
		};

		self.set(memory_offset, &data[..], Some(ulen))
	}
}

impl<IMemoryItem: MemoryItem> Memory<IMemoryItem> {
	/// Create a new memory with the given limit.
	fn internal_new(limit: usize, default_value: IMemoryItem) -> Self {
		Self {
			data: Vec::new(),
			effective_len: U256::zero(),
			limit,
			default_value,
		}
	}

	/// Memory limit.
	pub fn limit(&self) -> usize {
		self.limit
	}

	/// Get the length of the current memory range.
	pub fn len(&self) -> usize {
		self.data.len()
	}

	/// Get the effective length.
	pub fn effective_len(&self) -> U256 {
		self.effective_len
	}

	/// Return true if current effective memory range is zero.
	pub fn is_empty(&self) -> bool {
		self.len() == 0
	}

	/// Return the full memory.
	pub fn data(&self) -> &Vec<IMemoryItem> {
		&self.data
	}

	/// Resize the memory, making it cover the memory region of `offset..(offset
	/// + len)`, with 32 bytes as the step. If the length is zero, this function
	/// does nothing.
	pub fn resize_offset(&mut self, offset: U256, len: U256) -> Result<(), ExitError> {
		if len == U256::zero() {
			return Ok(());
		}

		if let Some(end) = offset.checked_add(len) {
			self.resize_end(end)
		} else {
			Err(ExitError::InvalidRange)
		}
	}

	/// Resize the memory, making it cover to `end`, with 32 bytes as the step.
	pub fn resize_end(&mut self, end: U256) -> Result<(), ExitError> {
		if end > self.effective_len {
			let new_end = next_multiple_of_32(end).ok_or(ExitError::InvalidRange)?;
			self.effective_len = new_end;
		}

		Ok(())
	}

	/// Get memory region at given offset.
	///
	/// ## Panics
	///
	/// Value of `size` is considered trusted. If they're too large,
	/// the program can run out of memory, or it can overflow.
	pub fn get(&self, offset: usize, size: usize) -> Vec<IMemoryItem> {
		let mut ret = Vec::new();
		ret.resize(size, self.default_value.clone());

		#[allow(clippy::needless_range_loop)]
		for index in 0..size {
			let position = offset + index;
			if position >= self.data.len() {
				break;
			}

			ret[index] = self.data[position].clone();
		}

		ret
	}

	/// Set memory region at given offset. The offset and value is considered
	/// untrusted.
	pub fn set(
		&mut self,
		offset: usize,
		value: &[IMemoryItem],
		target_size: Option<usize>,
	) -> Result<(), ExitFatal> {
		let target_size = target_size.unwrap_or(value.len());
		if target_size == 0 {
			return Ok(());
		}

		if offset
			.checked_add(target_size)
			.map(|pos| pos > self.limit)
			.unwrap_or(true)
		{
			return Err(ExitFatal::NotSupported);
		}

		if self.data.len() < offset + target_size {
			self.data
				.resize(offset + target_size, self.default_value.clone());
		}

		if target_size > value.len() {
			self.data[offset..((value.len()) + offset)].clone_from_slice(value);
			for index in (value.len())..target_size {
				self.data[offset + index] = self.default_value.clone();
			}
		} else {
			self.data[offset..(target_size + offset)].clone_from_slice(&value[..target_size]);
		}

		Ok(())
	}

	/// Copy `data` into the memory, of given `len`.
	pub fn copy_large(
		&mut self,
		memory_offset: U256,
		data_offset: U256,
		len: U256,
		data: &[IMemoryItem],
	) -> Result<(), ExitFatal> {
		// Needed to pass ethereum test defined in
		// https://github.com/ethereum/tests/commit/17f7e7a6c64bb878c1b6af9dc8371b46c133e46d
		// (regardless of other inputs, a zero-length copy is defined to be a no-op).
		// TODO: refactor `set` and `copy_large` (see
		// https://github.com/rust-blockchain/evm/pull/40#discussion_r677180794)
		if len.is_zero() {
			return Ok(());
		}

		let memory_offset = if memory_offset > U256::from(usize::MAX) {
			return Err(ExitFatal::NotSupported);
		} else {
			memory_offset.as_usize()
		};

		let ulen = if len > U256::from(usize::MAX) {
			return Err(ExitFatal::NotSupported);
		} else {
			len.as_usize()
		};

		let data = if let Some(end) = data_offset.checked_add(len) {
			if end > U256::from(usize::MAX) {
				&[]
			} else {
				let data_offset = data_offset.as_usize();
				let end = end.as_usize();

				if data_offset > data.len() {
					&[]
				} else {
					&data[data_offset..min(end, data.len())]
				}
			}
		} else {
			&[]
		};

		self.set(memory_offset, data, Some(ulen))
	}
}

/// Rounds up `x` to the closest multiple of 32. If `x % 32 == 0` then `x` is returned.
#[inline]
fn next_multiple_of_32(x: U256) -> Option<U256> {
	let r = x.low_u32().bitand(31).not().wrapping_add(1).bitand(31);
	x.checked_add(r.into())
}

#[cfg(test)]
mod tests {
	use super::{next_multiple_of_32, U256};

	#[test]
	fn test_next_multiple_of_32() {
		// next_multiple_of_32 returns x when it is a multiple of 32
		for i in 0..32 {
			let x = U256::from(i * 32);
			assert_eq!(Some(x), next_multiple_of_32(x));
		}

		// next_multiple_of_32 rounds up to the nearest multiple of 32 when `x % 32 != 0`
		for x in 0..1024 {
			if x % 32 == 0 {
				continue;
			}
			let next_multiple = x + 32 - (x % 32);
			assert_eq!(
				Some(U256::from(next_multiple)),
				next_multiple_of_32(x.into())
			);
		}

		// next_multiple_of_32 returns None when the next multiple of 32 is too big
		let last_multiple_of_32 = U256::MAX & !U256::from(31);
		for i in 0..63 {
			let x = U256::MAX - U256::from(i);
			if x > last_multiple_of_32 {
				assert_eq!(None, next_multiple_of_32(x));
			} else {
				assert_eq!(Some(last_multiple_of_32), next_multiple_of_32(x));
			}
		}
	}
}
