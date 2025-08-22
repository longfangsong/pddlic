use crate::pdc::{Action, Domain, Parameter, Predicate, Problem, Value, Variable};
use std::fmt;

impl fmt::Display for Parameter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "?{} - {}",
            self.name,
            self.data_type.as_ref().unwrap_or(&"object".to_string())
        )
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
        writeln!(
            f,
            "  :parameters ({})",
            self.parameters
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<_>>()
                .join(" ")
        )?;
        writeln!(
            f,
            "  :precondition {}",
            self.preconditions
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<_>>()
                .join(" ")
        )?;
        writeln!(
            f,
            "  :effect {}",
            self.effects
                .iter()
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

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} - {}", self.name, self.data_type.to_lowercase())
    }
}

impl fmt::Display for Problem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "(define (problem {})", self.name)?;
        writeln!(f, "  (:domain {})", self.domain.to_lowercase())?;

        // Objects - group by type
        if !self.variables.is_empty() {
            writeln!(f, "  (:objects")?;
            let mut type_groups: std::collections::HashMap<String, Vec<&Variable>> =
                std::collections::HashMap::new();
            for var in &self.variables {
                type_groups
                    .entry(var.data_type.to_lowercase())
                    .or_insert_with(Vec::new)
                    .push(var);
            }

            for (type_name, vars) in type_groups {
                let var_names: Vec<String> = vars.iter().map(|v| v.name.clone()).collect();
                writeln!(f, "    {} - {}", var_names.join(" "), type_name)?;
            }
            writeln!(f, "  )")?;
        }

        // Init
        if !self.init.is_empty() {
            writeln!(f, "")?;
            writeln!(f, "  (:init")?;
            for init_condition in &self.init {
                writeln!(f, "    {}", format_condition_for_problem(init_condition))?;
            }
            writeln!(f, "  )")?;
        }

        // Goal
        if !self.goal.is_empty() {
            writeln!(f, "")?;
            if self.goal.len() == 1 {
                writeln!(
                    f,
                    "  (:goal {})",
                    format_condition_for_problem(&self.goal[0])
                )?;
            } else {
                writeln!(f, "  (:goal (and")?;
                for goal_condition in &self.goal {
                    writeln!(f, "    {}", format_condition_for_problem(goal_condition))?;
                }
                writeln!(f, "  ))")?;
            }
        }

        write!(f, ")")
    }
}

fn format_condition_for_problem(value: &Value) -> String {
    match value {
        Value::Call(name, args) => {
            if args.is_empty() {
                format!("({})", name)
            } else {
                format!("({} {})", name, args.join(" "))
            }
        }
        Value::Not(v) => format!("(not {})", format_condition_for_problem(v)),
        Value::And(vs) => {
            if vs.len() == 1 {
                format_condition_for_problem(&vs[0])
            } else {
                format!(
                    "(and {})",
                    vs.iter()
                        .map(format_condition_for_problem)
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
        }
        Value::Or(vs) => {
            if vs.len() == 1 {
                format_condition_for_problem(&vs[0])
            } else {
                format!(
                    "(or {})",
                    vs.iter()
                        .map(format_condition_for_problem)
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
        }
    }
}

pub fn generate_pddl(domain: &Domain) -> String {
    domain.to_string()
}

pub fn generate_problem_pddl(problem: &Problem) -> String {
    problem.to_string()
}

pub fn generate_domain_and_problem_pddl(domain: &Domain, problem: &Problem) -> (String, String) {
    let domain_pddl = generate_pddl(domain);
    let problem_pddl = generate_problem_pddl(problem);
    (domain_pddl, problem_pddl)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_pddl() {
        let domain = Domain {
            name: "test".to_string(),
            types: vec![],
            predicates: vec![],
            actions: vec![Action {
                name: "test".to_string(),
                parameters: vec![],
                preconditions: vec![Value::And(vec![
                    Value::Call("at".to_string(), vec!["t".to_string(), "l".to_string()]),
                    Value::Call("at".to_string(), vec!["t".to_string(), "l".to_string()]),
                ])],
                effects: vec![Value::And(vec![
                    Value::Not(Box::new(Value::Call(
                        "at".to_string(),
                        vec!["t".to_string(), "l".to_string()],
                    ))),
                    Value::Call("at".to_string(), vec!["t".to_string(), "l".to_string()]),
                ])],
            }],
        };
        println!("{}", generate_pddl(&domain));
        // assert_eq!(true, false);
    }

    #[test]
    fn test_generate_problem_pddl() {
        let problem = Problem {
            name: "mixed-f2-p1-u0-v0-g0-a0-n0-A0-B0-N0-F0-r1".to_string(),
            domain: "miconic".to_string(),
            variables: vec![
                Variable {
                    name: "p0".to_string(),
                    data_type: "Passenger".to_string(),
                },
                Variable {
                    name: "f0".to_string(),
                    data_type: "Floor".to_string(),
                },
                Variable {
                    name: "f1".to_string(),
                    data_type: "Floor".to_string(),
                },
            ],
            init: vec![
                Value::Call(
                    "above".to_string(),
                    vec!["f0".to_string(), "f1".to_string()],
                ),
                Value::Call(
                    "origin".to_string(),
                    vec!["p0".to_string(), "f0".to_string()],
                ),
                Value::Call(
                    "destin".to_string(),
                    vec!["p0".to_string(), "f1".to_string()],
                ),
                Value::Call("lift-at".to_string(), vec!["f0".to_string()]),
            ],
            goal: vec![Value::Call("served".to_string(), vec!["p0".to_string()])],
        };

        let pddl = generate_problem_pddl(&problem);
        println!("Generated problem PDDL:\n{}", pddl);

        // Verify the output contains expected elements
        assert!(pddl.contains("(define (problem mixed-f2-p1-u0-v0-g0-a0-n0-A0-B0-N0-F0-r1)"));
        assert!(pddl.contains("(:domain miconic)"));
        assert!(pddl.contains("(:objects"));
        assert!(pddl.contains("p0 - passenger"));
        assert!(pddl.contains("f0 f1 - floor"));
        assert!(pddl.contains("(:init"));
        assert!(pddl.contains("(above f0 f1)"));
        assert!(pddl.contains("(origin p0 f0)"));
        assert!(pddl.contains("(destin p0 f1)"));
        assert!(pddl.contains("(lift-at f0)"));
        assert!(pddl.contains("(:goal (served p0))"));
    }

    #[test]
    fn test_generate_domain_and_problem_pddl() {
        let domain = Domain {
            name: "miconic".to_string(),
            types: vec![("Passenger".to_string(), None), ("Floor".to_string(), None)],
            predicates: vec![
                Predicate {
                    name: "lift-at".to_string(),
                    parameters: vec![Parameter {
                        name: "floor".to_string(),
                        data_type: Some("Floor".to_string()),
                    }],
                },
                Predicate {
                    name: "served".to_string(),
                    parameters: vec![Parameter {
                        name: "person".to_string(),
                        data_type: Some("Passenger".to_string()),
                    }],
                },
            ],
            actions: vec![],
        };

        let problem = Problem {
            name: "test-problem".to_string(),
            domain: "miconic".to_string(),
            variables: vec![
                Variable {
                    name: "p0".to_string(),
                    data_type: "Passenger".to_string(),
                },
                Variable {
                    name: "f0".to_string(),
                    data_type: "Floor".to_string(),
                },
            ],
            init: vec![Value::Call("lift-at".to_string(), vec!["f0".to_string()])],
            goal: vec![Value::Call("served".to_string(), vec!["p0".to_string()])],
        };

        let (domain_pddl, problem_pddl) = generate_domain_and_problem_pddl(&domain, &problem);

        println!("Generated domain PDDL:\n{}", domain_pddl);
        println!("Generated problem PDDL:\n{}", problem_pddl);

        // Verify domain contains expected elements
        assert!(domain_pddl.contains("(define (domain miconic)"));
        assert!(domain_pddl.contains("Passenger - object"));
        assert!(domain_pddl.contains("Floor - object"));

        // Verify problem contains expected elements
        assert!(problem_pddl.contains("(define (problem test-problem)"));
        assert!(problem_pddl.contains("(:domain miconic)"));
        assert!(problem_pddl.contains("p0 - passenger"));
        assert!(problem_pddl.contains("f0 - floor"));
    }
}
