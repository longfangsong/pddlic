use std::fmt;
use crate::pdc::{Action, Domain, Parameter, Predicate, Value};

impl fmt::Display for Parameter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "?{} - {}", self.name, self.data_type.as_ref().unwrap_or(&"object".to_string()))
    }
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}", self.name)?;
        for param in &self.parameters {
            write!(f, " {}", param)?;
        }
        write!(f, ")")
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Call(name, args) => {
                write!(f, "({}", name)?;
                for arg in args {
                    write!(f, " ?{}", arg)?;
                }
                write!(f, ")")
            }
            Value::Not(v) => write!(f, "(not {})", v),
            Value::And(vs) => {
                write!(f, "(and")?;
                for v in vs {
                    write!(f, " {}", v)?;
                }
                write!(f, ")")
            }
            Value::Or(vs) => {
                write!(f, "(or")?;
                for v in vs {
                    write!(f, " {}", v)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl fmt::Display for Action {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "(:action {}", self.name)?;
        writeln!(f, "  :parameters ({})", 
            self.parameters.iter()
                .map(|p| p.to_string())
                .collect::<Vec<_>>()
                .join(" ")
        )?;
        writeln!(f, "  :precondition {}", 
            self.preconditions.iter()
                .map(|p| p.to_string())
                .collect::<Vec<_>>()
                .join(" ")
        )?;
        writeln!(f, "  :effect {}", 
            self.effects.iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join(" ")
        )?;
        write!(f, ")")
    }
}

impl fmt::Display for Domain {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "(define (domain {})", self.name.to_lowercase())?;
        writeln!(f, "  (:requirements :strips :typing)")?;
        
        // Types
        writeln!(f, "  (:types")?;
        for (name, parent) in &self.types {
            if let Some(parent) = parent {
                writeln!(f, "    {} - {}", name, parent)?;
            } else {
                writeln!(f, "    {} - object", name)?;
            }
        }
        writeln!(f, "  )")?;
        
        // Predicates
        writeln!(f, "  (:predicates")?;
        for predicate in &self.predicates {
            writeln!(f, "    {}", predicate)?;
        }
        writeln!(f, "  )")?;
        
        // Actions
        for action in &self.actions {
            writeln!(f, "  {}", action)?;
        }
        
        write!(f, ")")
    }
}

pub fn generate_pddl(domain: &Domain) -> String {
    domain.to_string()
}

#[cfg(test)]
mod tests {
    use crate::pdc;

    use super::*;

    #[test]
    fn test_generate_pddl() {
        let domain = Domain {
            name: "test".to_string(),
            types: vec![],
            predicates: vec![],
            actions: vec![
                Action {
                    name: "test".to_string(),
                    parameters: vec![],
                    preconditions: vec![
                        Value::And(vec![
                            Value::Call("at".to_string(), vec!["t".to_string(), "l".to_string()]),
                            Value::Call("at".to_string(), vec!["t".to_string(), "l".to_string()]),
                        ]),
                    ],
                    effects: vec![
                        Value::And(vec![
                            Value::Not(Box::new(Value::Call("at".to_string(), vec!["t".to_string(), "l".to_string()]))),
                            Value::Call("at".to_string(), vec!["t".to_string(), "l".to_string()]),
                        ]),
                    ],
                },
            ],
        };
        println!("{}", generate_pddl(&domain));
        // assert_eq!(true, false);
    }
}