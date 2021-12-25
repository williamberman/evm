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

macro_rules! op2_sym_tuple_helper {
	( $machine:expr, $concrete_op:ident, $symbolic_op:expr, $sym_arg1:ident, $sym_arg2:ident ) => {{
		pop!($machine, op1, op2);

		let ret = match (op1, op2) {
			(SymStackItem::Concrete(xop1), SymStackItem::Concrete(xop2)) => {
				let v = U256::from_big_endian(&xop1[..])
					.$concrete_op(U256::from_big_endian(&xop2[..]))
					.0;

				let mut xv = H256::default();

				v.to_big_endian(&mut xv[..]);

				SymStackItem::Concrete(xv)
			}

			(SymStackItem::Concrete(xop1), SymStackItem::Symbolic($sym_arg2)) => {
				let $sym_arg1 = symbolic::bv_constant(xop1.as_bytes().to_vec());
				SymStackItem::Symbolic($symbolic_op.into())
			}

			(SymStackItem::Symbolic($sym_arg1), SymStackItem::Concrete(xop2)) => {
				let $sym_arg2 = symbolic::bv_constant(xop2.as_bytes().to_vec());
				SymStackItem::Symbolic($symbolic_op.into())
			}

			(SymStackItem::Symbolic($sym_arg1), SymStackItem::Symbolic($sym_arg2)) => {
				SymStackItem::Symbolic($symbolic_op.into())
			}
		};

		push!($machine, ret);

		Control::Continue(1)
	}};
}

macro_rules! op2_sym_fn_helper {
	( $machine:expr, $concrete_op:path, $symbolic_op:expr, $arg1:ident, $arg2:ident ) => {{
		pop!($machine, op1, op2);

		let ret = match (op1, op2) {
			(SymStackItem::Concrete(xop1), SymStackItem::Concrete(xop2)) => {
				let v = $concrete_op(
					U256::from_big_endian(&xop1[..]),
					U256::from_big_endian(&xop2[..]),
				);

				let mut xv = H256::default();

				v.to_big_endian(&mut xv[..]);

				SymStackItem::Concrete(xv)
			}

			(SymStackItem::Concrete(xop1), SymStackItem::Symbolic($arg2)) => {
				let $arg1 = symbolic::bv_constant(xop1.as_bytes().to_vec());
				SymStackItem::Symbolic($symbolic_op.into())
			}

			(SymStackItem::Symbolic($arg1), SymStackItem::Concrete(xop2)) => {
				let $arg2 = symbolic::bv_constant(xop2.as_bytes().to_vec());
				SymStackItem::Symbolic($symbolic_op.into())
			}

			(SymStackItem::Symbolic($arg1), SymStackItem::Symbolic($arg2)) => {
				SymStackItem::Symbolic($symbolic_op.into())
			}
		};

		push!($machine, ret);

		Control::Continue(1)
	}};
}

macro_rules! op2_sym_tuple_vec {
	( $machine:expr, $concrete_op:ident, $symbolic_op:path) => {{
		op2_sym_tuple_helper!(
			$machine,
			$concrete_op,
			$symbolic_op(smallvec![sym_arg1, sym_arg2]),
			sym_arg1,
			sym_arg2
		)
	}};
}

macro_rules! op2_sym_tuple_2_args {
	( $machine:expr, $concrete_op:ident, $symbolic_op:path) => {{
		op2_sym_tuple_helper!(
			$machine,
			$concrete_op,
			$symbolic_op(sym_arg1, sym_arg2),
			sym_arg1,
			sym_arg2
		)
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

macro_rules! op2_sym_fn {
	( $machine:expr, $concrete_op:path, $symbolic_op:path ) => {{
		op2_sym_fn_helper!(
			$machine,
			$concrete_op,
			$symbolic_op(sym_arg1, sym_arg2),
			sym_arg1,
			sym_arg2
		)
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
