use std::collections::BTreeMap;

use ethers::abi::{parse_abi, ParamType};
use evm::{
	backend::{MemoryBackend, MemoryVicinity},
	executor::stack::{MemoryStackState, StackExecutor, StackSubstateMetadata},
	Config, Context, SymbolicCalldata, SymbolicRuntime,
};
use primitive_types::{H160, U256};

use clap::Parser;

#[derive(Parser)]
struct Cli {
	#[clap(long)]
	sig: String,
	#[clap(long)]
	code: String,
	#[clap(long)]
	exit_code: u8,
}

fn main() {
	let args = Cli::parse();

	let code = hex::decode(args.code).unwrap();

	let abi = parse_abi(&[&args.sig])
		.unwrap()
		.functions
		.into_iter()
		.next()
		.unwrap()
		.1[0]
		.clone();

	let sel = abi.short_signature();

	let arg_length = abi.inputs.iter().fold(0, |acc, x| {
		acc + match x.kind {
			ParamType::Int(n) => n,
			ParamType::Uint(n) => n,
			_ => panic!("TODO unimplemented argument size"),
		}
	});

	let data = SymbolicCalldata::from_function_selector(&sel, arg_length);

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

	let machine = &rt.find_exit_code(args.exit_code).unwrap().borrow().machine;

	let cd = machine.solve();

	let xcd = abi.decode_input(&cd[4..]).unwrap();
	let args = xcd
		.into_iter()
		.map(|x| {
			// Only do string representation of uints for now
			x.into_uint().unwrap().to_string()
		})
		.collect::<Vec<String>>()
		.join(",");

    println!("Calldata:");
	println!("{}", hex::encode(cd.clone()));
	println!("{}({})", abi.name, args);
}
