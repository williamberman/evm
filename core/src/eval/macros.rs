macro_rules! try_or_fail {
	( $e:expr ) => {
		match $e {
			Ok(v) => v,
			Err(e) => return Control::Exit(e.into()),
		}
	};
}

macro_rules! pop {
	( $machine:expr, $( $x:ident ),* ) => (
		$(
			let $x = match $machine.stack.pop() {
				Ok(value) => value,
				Err(e) => return Control::Exit(e.into()),
			};
		)*
	);
}

macro_rules! pop_u256 {
	( $machine:expr, $( $x:ident ),* ) => (
		$(
			let $x = match $machine.stack.pop() {
				Ok(value) => U256::from_big_endian(&value[..]),
				Err(e) => return Control::Exit(e.into()),
			};
		)*
	);
}

macro_rules! push {
	( $machine:expr, $( $x:expr ),* ) => (
		$(
			match $machine.stack.push($x) {
				Ok(()) => (),
				Err(e) => return Control::Exit(e.into()),
			}
		)*
	)
}

macro_rules! push_u256 {
	( $machine:expr, $( $x:expr ),* ) => (
		$(
			let mut value = H256::default();
			$x.to_big_endian(&mut value[..]);
			match $machine.stack.push(value) {
				Ok(()) => (),
				Err(e) => return Control::Exit(e.into()),
			}
		)*
	)
}

macro_rules! op1_u256_fn {
	( $machine:expr, $op:path ) => {{
		pop_u256!($machine, op1);
		let ret = $op(op1);
		push_u256!($machine, ret);

		Control::Continue(1)
	}};
}

macro_rules! op2_u256_bool_ref {
	( $machine:expr, $op:ident ) => {{
		pop_u256!($machine, op1, op2);
		let ret = op1.$op(&op2);
		push_u256!($machine, if ret { U256::one() } else { U256::zero() });

		Control::Continue(1)
	}};
}

macro_rules! op2_u256 {
	( $machine:expr, $op:ident ) => {{
		pop_u256!($machine, op1, op2);
		let ret = op1.$op(op2);
		push_u256!($machine, ret);

		Control::Continue(1)
	}};
}

macro_rules! op2_u256_tuple {
	( $machine:expr, $op:ident ) => {{
		pop_u256!($machine, op1, op2);
		let (ret, ..) = op1.$op(op2);
		push_u256!($machine, ret);

		Control::Continue(1)
	}};
}

macro_rules! op2_u256_fn {
	( $machine:expr, $op:path ) => {{
		pop_u256!($machine, op1, op2);
		let ret = $op(op1, op2);
		push_u256!($machine, ret);

		Control::Continue(1)
	}};
}

macro_rules! op3_u256_fn {
	( $machine:expr, $op:path ) => {{
		pop_u256!($machine, op1, op2, op3);
		let ret = $op(op1, op2, op3);
		push_u256!($machine, ret);

		Control::Continue(1)
	}};
}

macro_rules! as_usize_or_fail {
	( $v:expr ) => {{
		if $v > U256::from(usize::MAX) {
			return Control::Exit(ExitFatal::NotSupported.into());
		}

		$v.as_usize()
	}};

	( $v:expr, $reason:expr ) => {{
		if $v > U256::from(usize::MAX) {
			return Control::Exit($reason.into());
		}

		$v.as_usize()
	}};
}

macro_rules! op2_sym_eval {
	($concrete_op:expr, $symbolic_op:expr) => {
		|state: &mut SymbolicMachine, _opcode: Opcode, _position: usize| -> Control {
			pop!(state, op1, op2);

			let ret = match (op1, op2) {
				(SymWord::Concrete(xop1), SymWord::Concrete(xop2)) => {
					SymWord::Concrete(uth(&$concrete_op(htu(&xop1), htu(&xop2))))
				}

				(SymWord::Concrete(xop1), SymWord::Symbolic(sym2)) => {
					let sym1 = symbolic::bv_constant_from_h256(&xop1);
					let v = $symbolic_op(sym1, sym2);
					SymWord::Symbolic(v.into())
				}

				(SymWord::Symbolic(sym1), SymWord::Concrete(xop2)) => {
					let sym2 = symbolic::bv_constant_from_h256(&xop2);
					let v = $symbolic_op(sym1, sym2);
					SymWord::Symbolic(v.into())
				}

				(SymWord::Symbolic(sym1), SymWord::Symbolic(sym2)) => {
					let v = $symbolic_op(sym1, sym2);
					SymWord::Symbolic(v.into())
				}
			};

			push!(state, ret);

			Control::Continue(1)
		}
	};
}

macro_rules! op2_evals_tuple_vec {
	( $name:ident, $concrete:ident, $symbolic:path) => {
		static $name: OpEvals = OpEvals {
			concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| {
				op2_u256_tuple!(state, $concrete)
			},
			symbolic: op2_sym_eval!(
				|op1: U256, op2: U256| { op1.$concrete(op2).0 },
				|sym1, sym2| { $symbolic(smallvec![sym1, sym2]) }
			),
		};
	};
}

macro_rules! op2_evals_tuple {
	( $name:ident, $concrete:ident, $symbolic:path) => {
		static $name: OpEvals = OpEvals {
			concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| {
				op2_u256_tuple!(state, $concrete)
			},
			symbolic: op2_sym_eval!(
				|op1: U256, op2: U256| { op1.$concrete(op2).0 },
				|sym1, sym2| { $symbolic(sym1, sym2) }
			),
		};
	};
}

macro_rules! op2_evals_x_vec {
	( $name:ident, $concrete:ident, $symbolic:path) => {
		static $name: OpEvals = OpEvals {
			concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| {
				op2_u256!(state, $concrete)
			},
			symbolic: op2_sym_eval!(
				|op1: U256, op2: U256| { op1.$concrete(op2) },
				|sym1, sym2| { $symbolic(smallvec![sym1, sym2]) }
			),
		};
	};
}

macro_rules! op2_evals_fn {
	( $name:ident, $concrete:path, $symbolic:path) => {
		static $name: OpEvals = OpEvals {
			concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| {
				op2_u256_fn!(state, $concrete)
			},
			symbolic: op2_sym_eval!(
				|op1: U256, op2: U256| { $concrete(op1, op2) },
				|sym1, sym2| { $symbolic(sym1, sym2) }
			),
		};
	};
}

macro_rules! op2_evals_bool_tuple {
	( $name:ident, $concrete:ident, $symbolic:path) => {
		static $name: OpEvals = OpEvals {
			concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| {
				op2_u256_bool_ref!(state, $concrete)
			},
			symbolic: op2_sym_eval!(
				|op1: U256, op2: U256| {
					if op1.$concrete(&op2) {
						U256::one()
					} else {
						U256::zero()
					}
				},
				|sym1, sym2| {
					CoreOp::Ite($symbolic(sym1, sym2).into(), bv_256_one(), bv_256_zero())
				}
			),
		};
	};
}

macro_rules! op2_evals_bool_tuple_vec {
	( $name:ident, $concrete:ident, $symbolic:path) => {
		static $name: OpEvals = OpEvals {
			concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| {
				op2_u256_bool_ref!(state, $concrete)
			},
			symbolic: op2_sym_eval!(
				|op1: U256, op2: U256| {
					if op1.$concrete(&op2) {
						U256::one()
					} else {
						U256::zero()
					}
				},
				|sym1, sym2| {
					CoreOp::Ite(
						$symbolic(smallvec![sym1, sym2]).into(),
						bv_256_one(),
						bv_256_zero(),
					)
				}
			),
		};
	};
}

macro_rules! op2_evals_bool_fn {
	( $name:ident, $concrete:path, $symbolic:path) => {
		static $name: OpEvals = OpEvals {
			concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| {
				op2_u256_fn!(state, $concrete)
			},
			symbolic: op2_sym_eval!($concrete, |sym1, sym2| {
				CoreOp::Ite($symbolic(sym1, sym2).into(), bv_256_one(), bv_256_zero())
			}),
		};
	};
}

macro_rules! dup_op {
	( $name:ident, $n:literal ) => {
		static $name: OpEvals = OpEvals {
			concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| -> Control {
				self::misc::dup(state, $n)
			},
			symbolic: |state: &mut SymbolicMachine, _opcode: Opcode, _position: usize| -> Control {
				self::misc::dup(state, $n)
			},
		};
	};
}

macro_rules! swap_op {
	( $name:ident, $n:literal ) => {
		static $name: OpEvals = OpEvals {
			concrete: |state: &mut ConcreteMachine, _opcode: Opcode, _position: usize| -> Control {
				self::misc::swap(state, $n)
			},
			symbolic: |state: &mut SymbolicMachine, _opcode: Opcode, _position: usize| -> Control {
				self::misc::swap(state, $n)
			},
		};
	};
}