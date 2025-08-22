mod parse;
pub use parse::{parse_pdc, parse_problem};

#[derive(Debug, Clone)]
pub struct Parameter {
    pub name: String,
    pub data_type: Option<String>,
}

#[derive(Debug, Clone)]
pub struct Predicate {
    pub name: String,
    pub parameters: Vec<Parameter>,
}

#[derive(Debug, Clone)]
pub struct Action {
    pub name: String,
    pub parameters: Vec<Parameter>,
    pub preconditions: Vec<Value>,
    pub effects: Vec<Value>,
}

#[derive(Debug, Clone)]
pub enum Value {
    And(Vec<Value>),
    Or(Vec<Value>),
    Not(Box<Value>),
    Call(String, Vec<String>),
}

#[derive(Debug, Clone)]
pub struct Domain {
    pub name: String,
    pub types: Vec<(String, Option<String>)>,
    pub predicates: Vec<Predicate>,
    pub actions: Vec<Action>,
}

#[derive(Debug, Clone)]
pub struct Variable {
    pub name: String,
    pub data_type: String,
}

#[derive(Debug, Clone)]
pub struct Problem {
    pub name: String,
    pub domain: String,
    pub variables: Vec<Variable>,
    pub init: Vec<Value>,
    pub goal: Vec<Value>,
}
