use std::fmt::{self, Debug};

use crate::symbolic::SymByte;

/// Opcode enum. One-to-one corresponding to an `u8` value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Opcode(pub u8);

impl fmt::Display for Opcode {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{}({:#02x})", OPCODE_STR_TABLE[self.as_usize()], self.0)
	}
}

// Core opcodes.
impl Opcode {
	/// `STOP`
	pub const STOP: Opcode = Opcode(0x00);
	/// `ADD`
	pub const ADD: Opcode = Opcode(0x01);
	/// `MUL`
	pub const MUL: Opcode = Opcode(0x02);
	/// `SUB`
	pub const SUB: Opcode = Opcode(0x03);
	/// `DIV`
	pub const DIV: Opcode = Opcode(0x04);
	/// `SDIV`
	pub const SDIV: Opcode = Opcode(0x05);
	/// `MOD`
	pub const MOD: Opcode = Opcode(0x06);
	/// `SMOD`
	pub const SMOD: Opcode = Opcode(0x07);
	/// `ADDMOD`
	pub const ADDMOD: Opcode = Opcode(0x08);
	/// `MULMOD`
	pub const MULMOD: Opcode = Opcode(0x09);
	/// `EXP`
	pub const EXP: Opcode = Opcode(0x0a);
	/// `SIGNEXTEND`
	pub const SIGNEXTEND: Opcode = Opcode(0x0b);

	/// `LT`
	pub const LT: Opcode = Opcode(0x10);
	/// `GT`
	pub const GT: Opcode = Opcode(0x11);
	/// `SLT`
	pub const SLT: Opcode = Opcode(0x12);
	/// `SGT`
	pub const SGT: Opcode = Opcode(0x13);
	/// `EQ`
	pub const EQ: Opcode = Opcode(0x14);
	/// `ISZERO`
	pub const ISZERO: Opcode = Opcode(0x15);
	/// `AND`
	pub const AND: Opcode = Opcode(0x16);
	/// `OR`
	pub const OR: Opcode = Opcode(0x17);
	/// `XOR`
	pub const XOR: Opcode = Opcode(0x18);
	/// `NOT`
	pub const NOT: Opcode = Opcode(0x19);
	/// `BYTE`
	pub const BYTE: Opcode = Opcode(0x1a);

	/// `CALLDATALOAD`
	pub const CALLDATALOAD: Opcode = Opcode(0x35);
	/// `CALLDATASIZE`
	pub const CALLDATASIZE: Opcode = Opcode(0x36);
	/// `CALLDATACOPY`
	pub const CALLDATACOPY: Opcode = Opcode(0x37);
	/// `CODESIZE`
	pub const CODESIZE: Opcode = Opcode(0x38);
	/// `CODECOPY`
	pub const CODECOPY: Opcode = Opcode(0x39);

	/// `SHL`
	pub const SHL: Opcode = Opcode(0x1b);
	/// `SHR`
	pub const SHR: Opcode = Opcode(0x1c);
	/// `SAR`
	pub const SAR: Opcode = Opcode(0x1d);

	/// `POP`
	pub const POP: Opcode = Opcode(0x50);
	/// `MLOAD`
	pub const MLOAD: Opcode = Opcode(0x51);
	/// `MSTORE`
	pub const MSTORE: Opcode = Opcode(0x52);
	/// `MSTORE8`
	pub const MSTORE8: Opcode = Opcode(0x53);
	/// `JUMP`
	pub const JUMP: Opcode = Opcode(0x56);
	/// `JUMPI`
	pub const JUMPI: Opcode = Opcode(0x57);
	/// `PC`
	pub const PC: Opcode = Opcode(0x58);
	/// `MSIZE`
	pub const MSIZE: Opcode = Opcode(0x59);
	/// `JUMPDEST`
	pub const JUMPDEST: Opcode = Opcode(0x5b);

	/// `PUSHn`
	pub const PUSH1: Opcode = Opcode(0x60);
	pub const PUSH2: Opcode = Opcode(0x61);
	pub const PUSH3: Opcode = Opcode(0x62);
	pub const PUSH4: Opcode = Opcode(0x63);
	pub const PUSH5: Opcode = Opcode(0x64);
	pub const PUSH6: Opcode = Opcode(0x65);
	pub const PUSH7: Opcode = Opcode(0x66);
	pub const PUSH8: Opcode = Opcode(0x67);
	pub const PUSH9: Opcode = Opcode(0x68);
	pub const PUSH10: Opcode = Opcode(0x69);
	pub const PUSH11: Opcode = Opcode(0x6a);
	pub const PUSH12: Opcode = Opcode(0x6b);
	pub const PUSH13: Opcode = Opcode(0x6c);
	pub const PUSH14: Opcode = Opcode(0x6d);
	pub const PUSH15: Opcode = Opcode(0x6e);
	pub const PUSH16: Opcode = Opcode(0x6f);
	pub const PUSH17: Opcode = Opcode(0x70);
	pub const PUSH18: Opcode = Opcode(0x71);
	pub const PUSH19: Opcode = Opcode(0x72);
	pub const PUSH20: Opcode = Opcode(0x73);
	pub const PUSH21: Opcode = Opcode(0x74);
	pub const PUSH22: Opcode = Opcode(0x75);
	pub const PUSH23: Opcode = Opcode(0x76);
	pub const PUSH24: Opcode = Opcode(0x77);
	pub const PUSH25: Opcode = Opcode(0x78);
	pub const PUSH26: Opcode = Opcode(0x79);
	pub const PUSH27: Opcode = Opcode(0x7a);
	pub const PUSH28: Opcode = Opcode(0x7b);
	pub const PUSH29: Opcode = Opcode(0x7c);
	pub const PUSH30: Opcode = Opcode(0x7d);
	pub const PUSH31: Opcode = Opcode(0x7e);
	pub const PUSH32: Opcode = Opcode(0x7f);

	/// `DUPn`
	pub const DUP1: Opcode = Opcode(0x80);
	pub const DUP2: Opcode = Opcode(0x81);
	pub const DUP3: Opcode = Opcode(0x82);
	pub const DUP4: Opcode = Opcode(0x83);
	pub const DUP5: Opcode = Opcode(0x84);
	pub const DUP6: Opcode = Opcode(0x85);
	pub const DUP7: Opcode = Opcode(0x86);
	pub const DUP8: Opcode = Opcode(0x87);
	pub const DUP9: Opcode = Opcode(0x88);
	pub const DUP10: Opcode = Opcode(0x89);
	pub const DUP11: Opcode = Opcode(0x8a);
	pub const DUP12: Opcode = Opcode(0x8b);
	pub const DUP13: Opcode = Opcode(0x8c);
	pub const DUP14: Opcode = Opcode(0x8d);
	pub const DUP15: Opcode = Opcode(0x8e);
	pub const DUP16: Opcode = Opcode(0x8f);

	/// `SWAPn`
	pub const SWAP1: Opcode = Opcode(0x90);
	pub const SWAP2: Opcode = Opcode(0x91);
	pub const SWAP3: Opcode = Opcode(0x92);
	pub const SWAP4: Opcode = Opcode(0x93);
	pub const SWAP5: Opcode = Opcode(0x94);
	pub const SWAP6: Opcode = Opcode(0x95);
	pub const SWAP7: Opcode = Opcode(0x96);
	pub const SWAP8: Opcode = Opcode(0x97);
	pub const SWAP9: Opcode = Opcode(0x98);
	pub const SWAP10: Opcode = Opcode(0x99);
	pub const SWAP11: Opcode = Opcode(0x9a);
	pub const SWAP12: Opcode = Opcode(0x9b);
	pub const SWAP13: Opcode = Opcode(0x9c);
	pub const SWAP14: Opcode = Opcode(0x9d);
	pub const SWAP15: Opcode = Opcode(0x9e);
	pub const SWAP16: Opcode = Opcode(0x9f);

	/// `RETURN`
	pub const RETURN: Opcode = Opcode(0xf3);
	/// `REVERT`
	pub const REVERT: Opcode = Opcode(0xfd);

	/// `INVALID`
	pub const INVALID: Opcode = Opcode(0xfe);
}

// External opcodes
impl Opcode {
	/// `SHA3`
	pub const SHA3: Opcode = Opcode(0x20);
	/// `ADDRESS`
	pub const ADDRESS: Opcode = Opcode(0x30);
	/// `BALANCE`
	pub const BALANCE: Opcode = Opcode(0x31);
	/// `SELFBALANCE`
	pub const SELFBALANCE: Opcode = Opcode(0x47);
	/// `BASEFEE`
	pub const BASEFEE: Opcode = Opcode(0x48);
	/// `ORIGIN`
	pub const ORIGIN: Opcode = Opcode(0x32);
	/// `CALLER`
	pub const CALLER: Opcode = Opcode(0x33);
	/// `CALLVALUE`
	pub const CALLVALUE: Opcode = Opcode(0x34);
	/// `GASPRICE`
	pub const GASPRICE: Opcode = Opcode(0x3a);
	/// `EXTCODESIZE`
	pub const EXTCODESIZE: Opcode = Opcode(0x3b);
	/// `EXTCODECOPY`
	pub const EXTCODECOPY: Opcode = Opcode(0x3c);
	/// `EXTCODEHASH`
	pub const EXTCODEHASH: Opcode = Opcode(0x3f);
	/// `RETURNDATASIZE`
	pub const RETURNDATASIZE: Opcode = Opcode(0x3d);
	/// `RETURNDATACOPY`
	pub const RETURNDATACOPY: Opcode = Opcode(0x3e);
	/// `BLOCKHASH`
	pub const BLOCKHASH: Opcode = Opcode(0x40);
	/// `COINBASE`
	pub const COINBASE: Opcode = Opcode(0x41);
	/// `TIMESTAMP`
	pub const TIMESTAMP: Opcode = Opcode(0x42);
	/// `NUMBER`
	pub const NUMBER: Opcode = Opcode(0x43);
	/// `DIFFICULTY`
	pub const DIFFICULTY: Opcode = Opcode(0x44);
	/// `GASLIMIT`
	pub const GASLIMIT: Opcode = Opcode(0x45);
	/// `SLOAD`
	pub const SLOAD: Opcode = Opcode(0x54);
	/// `SSTORE`
	pub const SSTORE: Opcode = Opcode(0x55);
	/// `GAS`
	pub const GAS: Opcode = Opcode(0x5a);
	/// `LOGn`
	pub const LOG0: Opcode = Opcode(0xa0);
	pub const LOG1: Opcode = Opcode(0xa1);
	pub const LOG2: Opcode = Opcode(0xa2);
	pub const LOG3: Opcode = Opcode(0xa3);
	pub const LOG4: Opcode = Opcode(0xa4);
	/// `CREATE`
	pub const CREATE: Opcode = Opcode(0xf0);
	/// `CREATE2`
	pub const CREATE2: Opcode = Opcode(0xf5);
	/// `CALL`
	pub const CALL: Opcode = Opcode(0xf1);
	/// `CALLCODE`
	pub const CALLCODE: Opcode = Opcode(0xf2);
	/// `DELEGATECALL`
	pub const DELEGATECALL: Opcode = Opcode(0xf4);
	/// `STATICCALL`
	pub const STATICCALL: Opcode = Opcode(0xfa);
	/// `SUICIDE`
	pub const SUICIDE: Opcode = Opcode(0xff);
	/// `CHAINID`
	pub const CHAINID: Opcode = Opcode(0x46);
}

impl Opcode {
	/// Whether the opcode is a push opcode.
	pub fn is_push(&self) -> Option<u8> {
		let value = self.0;
		if (0x60..=0x7f).contains(&value) {
			Some(value - 0x60 + 1)
		} else {
			None
		}
	}

	#[inline]
	pub const fn as_u8(&self) -> u8 {
		self.0
	}

	#[inline]
	pub const fn as_usize(&self) -> usize {
		self.0 as usize
	}
}

impl From<u8> for Opcode {
	fn from(x: u8) -> Self {
		Opcode(x)
	}
}

impl From<SymByte> for Opcode {
	fn from(x: SymByte) -> Self {
		match x {
			SymByte::Concrete(x) => Opcode::from(x),
			_ => panic!("can only create opcode from concrete byte"),
		}
	}
}

pub static OPCODE_STR_TABLE: [&str; 256] = {
	let mut table = ["UNKNOWN"; 256];
	table[Opcode::STOP.as_usize()] = "STOP";
	table[Opcode::ADD.as_usize()] = "ADD";
	table[Opcode::MUL.as_usize()] = "MUL";
	table[Opcode::SUB.as_usize()] = "SUB";
	table[Opcode::DIV.as_usize()] = "DIV";
	table[Opcode::SDIV.as_usize()] = "SDIV";
	table[Opcode::MOD.as_usize()] = "MOD";
	table[Opcode::SMOD.as_usize()] = "SMOD";
	table[Opcode::ADDMOD.as_usize()] = "ADDMOD";
	table[Opcode::MULMOD.as_usize()] = "MULMOD";
	table[Opcode::EXP.as_usize()] = "EXP";
	table[Opcode::SIGNEXTEND.as_usize()] = "SIGNEXTEND";
	table[Opcode::LT.as_usize()] = "LT";
	table[Opcode::GT.as_usize()] = "GT";
	table[Opcode::SLT.as_usize()] = "SLT";
	table[Opcode::SGT.as_usize()] = "SGT";
	table[Opcode::EQ.as_usize()] = "EQ";
	table[Opcode::ISZERO.as_usize()] = "ISZERO";
	table[Opcode::AND.as_usize()] = "AND";
	table[Opcode::OR.as_usize()] = "OR";
	table[Opcode::XOR.as_usize()] = "XOR";
	table[Opcode::NOT.as_usize()] = "NOT";
	table[Opcode::BYTE.as_usize()] = "BYTE";
	table[Opcode::CALLDATALOAD.as_usize()] = "CALLDATALOAD";
	table[Opcode::CALLDATASIZE.as_usize()] = "CALLDATASIZE";
	table[Opcode::CALLDATACOPY.as_usize()] = "CALLDATACOPY";
	table[Opcode::CODESIZE.as_usize()] = "CODESIZE";
	table[Opcode::CODECOPY.as_usize()] = "CODECOPY";
	table[Opcode::SHL.as_usize()] = "SHL";
	table[Opcode::SHR.as_usize()] = "SHR";
	table[Opcode::SAR.as_usize()] = "SAR";
	table[Opcode::POP.as_usize()] = "POP";
	table[Opcode::MLOAD.as_usize()] = "MLOAD";
	table[Opcode::MSTORE.as_usize()] = "MSTORE";
	table[Opcode::MSTORE8.as_usize()] = "MSTORE8";
	table[Opcode::JUMP.as_usize()] = "JUMP";
	table[Opcode::JUMPI.as_usize()] = "JUMPI";
	table[Opcode::PC.as_usize()] = "PC";
	table[Opcode::MSIZE.as_usize()] = "MSIZE";
	table[Opcode::JUMPDEST.as_usize()] = "JUMPDEST";
	table[Opcode::PUSH1.as_usize()] = "PUSH1";
	table[Opcode::PUSH2.as_usize()] = "PUSH2";
	table[Opcode::PUSH3.as_usize()] = "PUSH3";
	table[Opcode::PUSH4.as_usize()] = "PUSH4";
	table[Opcode::PUSH5.as_usize()] = "PUSH5";
	table[Opcode::PUSH6.as_usize()] = "PUSH6";
	table[Opcode::PUSH7.as_usize()] = "PUSH7";
	table[Opcode::PUSH8.as_usize()] = "PUSH8";
	table[Opcode::PUSH9.as_usize()] = "PUSH9";
	table[Opcode::PUSH10.as_usize()] = "PUSH10";
	table[Opcode::PUSH11.as_usize()] = "PUSH11";
	table[Opcode::PUSH12.as_usize()] = "PUSH12";
	table[Opcode::PUSH13.as_usize()] = "PUSH13";
	table[Opcode::PUSH14.as_usize()] = "PUSH14";
	table[Opcode::PUSH15.as_usize()] = "PUSH15";
	table[Opcode::PUSH16.as_usize()] = "PUSH16";
	table[Opcode::PUSH17.as_usize()] = "PUSH17";
	table[Opcode::PUSH18.as_usize()] = "PUSH18";
	table[Opcode::PUSH19.as_usize()] = "PUSH19";
	table[Opcode::PUSH20.as_usize()] = "PUSH20";
	table[Opcode::PUSH21.as_usize()] = "PUSH21";
	table[Opcode::PUSH22.as_usize()] = "PUSH22";
	table[Opcode::PUSH23.as_usize()] = "PUSH23";
	table[Opcode::PUSH24.as_usize()] = "PUSH24";
	table[Opcode::PUSH25.as_usize()] = "PUSH25";
	table[Opcode::PUSH26.as_usize()] = "PUSH26";
	table[Opcode::PUSH27.as_usize()] = "PUSH27";
	table[Opcode::PUSH28.as_usize()] = "PUSH28";
	table[Opcode::PUSH29.as_usize()] = "PUSH29";
	table[Opcode::PUSH30.as_usize()] = "PUSH30";
	table[Opcode::PUSH31.as_usize()] = "PUSH31";
	table[Opcode::PUSH32.as_usize()] = "PUSH32";
	table[Opcode::DUP1.as_usize()] = "DUP1";
	table[Opcode::DUP2.as_usize()] = "DUP2";
	table[Opcode::DUP3.as_usize()] = "DUP3";
	table[Opcode::DUP4.as_usize()] = "DUP4";
	table[Opcode::DUP5.as_usize()] = "DUP5";
	table[Opcode::DUP6.as_usize()] = "DUP6";
	table[Opcode::DUP7.as_usize()] = "DUP7";
	table[Opcode::DUP8.as_usize()] = "DUP8";
	table[Opcode::DUP9.as_usize()] = "DUP9";
	table[Opcode::DUP10.as_usize()] = "DUP10";
	table[Opcode::DUP11.as_usize()] = "DUP11";
	table[Opcode::DUP12.as_usize()] = "DUP12";
	table[Opcode::DUP13.as_usize()] = "DUP13";
	table[Opcode::DUP14.as_usize()] = "DUP14";
	table[Opcode::DUP15.as_usize()] = "DUP15";
	table[Opcode::DUP16.as_usize()] = "DUP16";
	table[Opcode::SWAP1.as_usize()] = "SWAP1";
	table[Opcode::SWAP2.as_usize()] = "SWAP2";
	table[Opcode::SWAP3.as_usize()] = "SWAP3";
	table[Opcode::SWAP4.as_usize()] = "SWAP4";
	table[Opcode::SWAP5.as_usize()] = "SWAP5";
	table[Opcode::SWAP6.as_usize()] = "SWAP6";
	table[Opcode::SWAP7.as_usize()] = "SWAP7";
	table[Opcode::SWAP8.as_usize()] = "SWAP8";
	table[Opcode::SWAP9.as_usize()] = "SWAP9";
	table[Opcode::SWAP10.as_usize()] = "SWAP10";
	table[Opcode::SWAP11.as_usize()] = "SWAP11";
	table[Opcode::SWAP12.as_usize()] = "SWAP12";
	table[Opcode::SWAP13.as_usize()] = "SWAP13";
	table[Opcode::SWAP14.as_usize()] = "SWAP14";
	table[Opcode::SWAP15.as_usize()] = "SWAP15";
	table[Opcode::SWAP16.as_usize()] = "SWAP16";
	table[Opcode::RETURN.as_usize()] = "RETURN";
	table[Opcode::REVERT.as_usize()] = "REVERT";
	table[Opcode::INVALID.as_usize()] = "INVALID";
	table[Opcode::SHA3.as_usize()] = "SHA3";
	table[Opcode::ADDRESS.as_usize()] = "ADDRESS";
	table[Opcode::BALANCE.as_usize()] = "BALANCE";
	table[Opcode::SELFBALANCE.as_usize()] = "SELFBALANCE";
	table[Opcode::BASEFEE.as_usize()] = "BASEFEE";
	table[Opcode::ORIGIN.as_usize()] = "ORIGIN";
	table[Opcode::CALLER.as_usize()] = "CALLER";
	table[Opcode::CALLVALUE.as_usize()] = "CALLVALUE";
	table[Opcode::GASPRICE.as_usize()] = "GASPRICE";
	table[Opcode::EXTCODESIZE.as_usize()] = "EXTCODESIZE";
	table[Opcode::EXTCODECOPY.as_usize()] = "EXTCODECOPY";
	table[Opcode::EXTCODEHASH.as_usize()] = "EXTCODEHASH";
	table[Opcode::RETURNDATASIZE.as_usize()] = "RETURNDATASIZE";
	table[Opcode::RETURNDATACOPY.as_usize()] = "RETURNDATACOPY";
	table[Opcode::BLOCKHASH.as_usize()] = "BLOCKHASH";
	table[Opcode::COINBASE.as_usize()] = "COINBASE";
	table[Opcode::TIMESTAMP.as_usize()] = "TIMESTAMP";
	table[Opcode::NUMBER.as_usize()] = "NUMBER";
	table[Opcode::DIFFICULTY.as_usize()] = "DIFFICULTY";
	table[Opcode::GASLIMIT.as_usize()] = "GASLIMIT";
	table[Opcode::SLOAD.as_usize()] = "SLOAD";
	table[Opcode::SSTORE.as_usize()] = "SSTORE";
	table[Opcode::GAS.as_usize()] = "GAS";
	table[Opcode::LOG0.as_usize()] = "LOG0";
	table[Opcode::LOG1.as_usize()] = "LOG1";
	table[Opcode::LOG2.as_usize()] = "LOG2";
	table[Opcode::LOG3.as_usize()] = "LOG3";
	table[Opcode::LOG4.as_usize()] = "LOG4";
	table[Opcode::CREATE.as_usize()] = "CREATE";
	table[Opcode::CREATE2.as_usize()] = "CREATE2";
	table[Opcode::CALL.as_usize()] = "CALL";
	table[Opcode::CALLCODE.as_usize()] = "CALLCODE";
	table[Opcode::DELEGATECALL.as_usize()] = "DELEGATECALL";
	table[Opcode::STATICCALL.as_usize()] = "STATICCALL";
	table[Opcode::SUICIDE.as_usize()] = "SUICIDE";
	table[Opcode::CHAINID.as_usize()] = "CHAINID";
	table
};
