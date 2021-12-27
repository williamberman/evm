// TODO remove deadcode allows

use std::{fmt::Display, ops::Deref, convert::TryFrom};

use amzn_smt_ir::{
    logic::ALL, Binary, Command, Constant, Decimal, Hexadecimal, IConst, ISort, ISymbol, Numeral,
    Script, Term,
};
use num::{self, bigint::ToBigUint};

#[allow(dead_code)]
pub fn int_constant<T: ToBigUint>(x: T) -> Term<ALL> {
    return Term::Constant(IConst::from(Constant::Numeral(x.to_biguint().unwrap())));
}

// Note, Constant::Hexadecimal says it expects nibbles, but it's hungry enough you can feed it full bytes
pub fn bv_constant(x: Hexadecimal) -> Term<ALL> {
    return Term::Constant(IConst::from(Constant::Hexadecimal(x)));
}

#[allow(dead_code)]
// TODO probably better way to do this.
pub fn bv_512_zero() -> Term<ALL> {
    let x: [u8; 128] = [
        0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
    ];

    bv_constant(x.to_vec())
}

// TODO probably better way to do this.
pub fn bv_256_zero() -> Term<ALL> {
    let x: [u8; 64] = [
        0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
    ];

    bv_constant(x.to_vec())
}

#[allow(dead_code)]
// TODO make generic
fn script(variables: &[(Term<ALL>, ISort)], assertions: &[Term<ALL>]) -> Script<Term<ALL>> {
    let mut s = Script::new();

    // Variable declarations
    s.extend(variables.iter().map(|(t, sort)| match t {
        Term::Variable(x) => Command::<Term>::DeclareConst {
            symbol: x.to_string().into(),
            sort: sort.clone(),
        },
        _ => todo!(),
    }));

    // Assertions
    s.add_asserts(assertions.into_iter().map(|a| a.clone()));

    // Check satisfiable and get solution
    s.extend(vec![
        Command::CheckSat,
        Command::GetValue {
            terms: variables.iter().map(|(t, ..)| t.clone()).collect(),
        },
        Command::Exit,
    ]);

    return s;
}

#[derive(Debug)]
pub struct Solution {
    #[allow(dead_code)]
    bindings: Vec<(ISymbol, Term)>,
}

#[derive(Debug, Clone)]
pub struct UnsatError;

impl TryFrom<Script<Term<ALL>>> for Solution {
    type Error = UnsatError;

    fn try_from(s: Script<Term<ALL>>) -> Result<Self, Self::Error> {
        return Ok(Solution {
            bindings: solve(s)?,
        });
    }
}

impl Solution {
    #[allow(dead_code)]
    pub fn try_new(
        variables: &[(Term<ALL>, ISort)],
        assertions: &[Term<ALL>],
    ) -> Result<Self, UnsatError> {
        let s = script(variables, assertions);
        return Self::try_from(s);
    }

    #[allow(dead_code)]
    pub fn get(&self, t: &Term) -> Option<Native> {
        match t {
            Term::Variable(x) => {
                let sym: ISymbol = x.to_string().into();

                // TODO -- why does it say b is a double reference
                let found = &self.bindings.iter().find(|b| b.0 == sym)?.1;

                return Some(Native::from(found));
            }

            _ => {
                panic!("{} {:?}", "Can only look up variables in solutions", "t")
            }
        }
    }
}

fn solve(s: Script<Term<ALL>>) -> Result<Vec<(ISymbol, Term)>, UnsatError> {
    // TODO generate new filename every time.
    // TODO system agnostic temp directory
    let filename = "/tmp/out.smtlib";

    std::fs::write(filename, s.to_string()).unwrap();

    let out = std::process::Command::new("z3")
        .arg(filename)
        .output()
        .unwrap();

    let xout = String::from_utf8(out.stdout).unwrap();
    let error_msg = format!("{} {}", "Unsat could not parse sat solver output", xout);

    let mut lines = xout.lines();
    let first_line = lines.next().ok_or(&error_msg).unwrap();

    if out.status.success() && first_line == "sat" {
        let rest = lines.collect::<Vec<&str>>().join("\n");
        return Ok(parse_bindings(parse_term(&rest)));
    } else if !out.status.success() && first_line == "unsat" {
        return Err(UnsatError);
    } else {
        panic!("{}", error_msg);
    }
}

fn parse_bindings(term: Term) -> Vec<(ISymbol, Term)> {
    match term {
        Term::Let(l) => {
            return l.bindings.clone();
        }

        _ => {
            panic!("{} {:?}", "Can only parse bindings out of let term", term)
        }
    }
}

fn parse_term(smt: &str) -> Term {
    let smt = format!("(assert (let {} 1))", smt);

    let s = Script::<Term>::parse(smt.as_bytes()).unwrap();

    return s.into_asserted_terms().next().unwrap();
}

// Right now we're just unpacking and re-packing. But I assume ultimately we will
// want to wrap values from additional types in one native type variant.
#[derive(Debug)]
pub enum Native {
    Numeral(Numeral),
    Decimal(Decimal),
    Hexadecimal(Hexadecimal),
    Binary(Binary),
    String(String),
}

impl Display for Native {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Native::Numeral(n) => {
                write!(f, "{}", n)
            }
            Native::Decimal(n) => {
                write!(f, "{}", n)
            }
            Native::Hexadecimal(n) => {
                let mut h = hex::encode(nibbles_to_bytes(n));

                if h.as_bytes()[0] == '0' as u8 {
                    h.remove(0);
                }

                write!(f, "#x{}", h)
            }
            Native::Binary(_n) => {
                write!(f, "{}", "TODO")
            }
            Native::String(n) => {
                write!(f, "{}", n)
            }
        }
    }
}

fn nibbles_to_bytes(n: &Vec<u8>) -> Vec<u8> {
    let mut rv = vec![];

    let mut i = n.len() - 1;

    loop {
        if i == 0 {
            rv.push(n[i]);
            break;
        } else {
            rv.push(16 * n[i - 1] + n[i]);
            if i == 1 {
                break;
            } else {
                i -= 2;
            }
        }
    }

    rv.reverse();

    return rv;
}

impl From<&Term> for Native {
    fn from(t: &Term) -> Self {
        match t {
            Term::Constant(tt) => match tt.deref() {
                Constant::Numeral(n) => Native::Numeral(n.clone()),
                Constant::Decimal(n) => Native::Decimal(n.clone()),
                Constant::Hexadecimal(n) => Native::Hexadecimal(n.clone()),
                Constant::Binary(n) => Native::Binary(n.clone()),
                Constant::String(s) => Native::String(s.clone()),
            },
            _ => {
                panic!("{} {:?}", "Cannot convert non-term into native", t)
            }
        }
    }
}
