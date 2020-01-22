use std::io::{Read, Write};
use std::process::{Command, Stdio};

pub fn call(code: &str) -> Result<CheckResult, Box<dyn std::error::Error>> {
    let mut buffer = String::new();

    let child =
        Command::new("z3").arg("-in").stdin(Stdio::piped()).stdout(Stdio::piped()).spawn()?;

    child.stdin.expect("stdin is none").write(code.as_bytes())?;

    child.stdout.expect("stdout is none").read_to_string(&mut buffer)?;

    Ok(CheckResult::from_string(buffer))
}

#[derive(Debug, PartialEq, Eq)]
pub enum CheckResult {
    Sat,
    Unsat,
    Undecided,
    Unknown(String),
}

impl CheckResult {
    fn from_string(s: String) -> Self {
        if s == "sat\n" {
            CheckResult::Sat
        } else if s == "unsat\n" {
            CheckResult::Unsat
        } else if s == "unknown\n" {
            CheckResult::Undecided
        } else {
            CheckResult::Unknown(s)
        }
    }
}
