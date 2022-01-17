//! Ethereum Virtual Machine implementation in Rust

#![deny(warnings)]
#![forbid(unsafe_code, unused_variables)]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

pub use evm_core::*;
pub use evm_gasometer as gasometer;
pub use evm_runtime::*;

#[cfg(feature = "tracing")]
pub mod tracing;

#[cfg(feature = "tracing")]
macro_rules! event {
	($x:expr) => {
		use crate::tracing::Event::*;
		crate::tracing::with(|listener| listener.event($x));
	};
}

#[cfg(not(feature = "tracing"))]
macro_rules! event {
	($x:expr) => {};
}

pub mod backend;
pub mod executor;

#[cfg(test)]
mod tests {
	use std::collections::BTreeMap;

	use crate::backend::MemoryBackend;
	use crate::backend::MemoryVicinity;
	use crate::executor::stack::MemoryStackState;
	use crate::executor::stack::StackExecutor;
	use crate::executor::stack::StackSubstateMetadata;
	use crate::Config;
	use crate::Context;
	use crate::SymbolicRuntime;
	use evm_core::SymbolicCalldata;
	use primitive_types::H160;
	use primitive_types::U256;

	#[test]
	fn test_data() {
		let data =
			SymbolicCalldata::from_function_selector(hex::decode("d5a24249").unwrap(), 2 * 256);

		println!("{:?}", data.elements);
	}

	#[test]
	fn test_symbolic_runtime() {
		let code = hex::decode("608060405234801561001057600080fd5b506004361061002b5760003560e01c8063d5a2424914610030575b600080fd5b61004a600480360381019061004591906100df565b61004c565b005b81600110801561005e5750620ed8d582105b801561006a5750806001105b80156100785750620ed8d581105b61008157600080fd5b620ed8d58183610091919061014e565b14156100a05761009f6101a8565b5b5050565b600080fd5b6000819050919050565b6100bc816100a9565b81146100c757600080fd5b50565b6000813590506100d9816100b3565b92915050565b600080604083850312156100f6576100f56100a4565b5b6000610104858286016100ca565b9250506020610115858286016100ca565b9150509250929050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601160045260246000fd5b6000610159826100a9565b9150610164836100a9565b9250817fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff048311821515161561019d5761019c61011f565b5b828202905092915050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052600160045260246000fdfea26469706673582212202c667a96599f0a0921c5454871e3ebdb6434748a412b3bf97324ce0d32ec5fe864736f6c63430008090033").unwrap();

		// Symbolic
		let data =
			SymbolicCalldata::from_function_selector(hex::decode("d5a24249").unwrap(), 2 * 256);

		// Fail
		// let data = SymbolicCalldata::from(hex::decode("d5a2424900000000000000000000000000000000000000000000000000000000000003fd00000000000000000000000000000000000000000000000000000000000003b9").unwrap());

		// Succeed
		// let data = SymbolicCalldata::from(hex::decode("d5a2424900000000000000000000000000000000000000000000000000000000000003fe00000000000000000000000000000000000000000000000000000000000003b9").unwrap());

		let ctx = Context {
			address: H160::zero(),
			caller: H160::zero(),
			apparent_value: U256::zero(),
		};

		let config = Config::london();

		let mut rt = SymbolicRuntime::new(code, data, ctx, &config);

		let vicinity = MemoryVicinity {
			gas_price: U256::zero(),
			origin: H160::default(),
			block_hashes: Vec::new(),
			block_number: Default::default(),
			block_coinbase: Default::default(),
			block_timestamp: Default::default(),
			block_difficulty: Default::default(),
			block_gas_limit: Default::default(),
			chain_id: U256::one(),
			block_base_fee_per_gas: U256::zero(),
		};

		let state = BTreeMap::new();

		let backend = MemoryBackend::new(&vicinity, state);
		let metadata = StackSubstateMetadata::new(u64::MAX, &config);
		let state = MemoryStackState::new(metadata, &backend);
		let precompiles = BTreeMap::new();
		let mut executor = StackExecutor::new_with_precompiles(state, &config, &precompiles);

		rt.run(&mut executor);

		// println!("{}", rt.machines.len());

		// for m in rt.machines.iter() {
		// 	println!("{:?}", m.borrow().status);
		// }

		let machine = &rt.machines.get(0).unwrap().borrow_mut().machine;

		// println!("************");
		// println!("{:?}", machine.return_value());
		// println!("************");

		let cd = machine.solve();


		// println!("{}", hex::encode(cd.clone()));
		assert_eq!(hex::encode(cd.clone()), "d5a2424900000000000000000000000000000000000000000000000000000000000003b900000000000000000000000000000000000000000000000000000000000003fd")
	}
}
