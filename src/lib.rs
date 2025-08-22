pub mod pdc;
pub mod pddl;

use pdc::{parse_pdc, parse_problem};
use pddl::{generate_domain_and_problem_pddl, generate_pddl, generate_problem_pddl};
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn pdc_to_pddl(pdc_code: &str) -> Result<String, JsValue> {
    let domain =
        parse_pdc(pdc_code).map_err(|e| JsValue::from_str(&format!("Parse error: {}", e)))?;

    let pddl = generate_pddl(&domain);
    Ok(pddl)
}

#[wasm_bindgen]
pub fn parse_pdc_problem(problem_code: &str) -> Result<String, JsValue> {
    let problem = parse_problem(problem_code)
        .map_err(|e| JsValue::from_str(&format!("Parse error: {}", e)))?;

    // Return a JSON representation or debug format for now
    Ok(format!("{:?}", problem))
}

#[wasm_bindgen]
pub fn problem_to_pddl(problem_code: &str, domain_name: &str) -> Result<String, JsValue> {
    let mut problem = parse_problem(problem_code)
        .map_err(|e| JsValue::from_str(&format!("Parse error: {}", e)))?;

    // Set the domain name only if not already specified in the problem definition
    if problem.domain.is_empty() && !domain_name.is_empty() {
        problem.domain = domain_name.to_string();
    }

    let pddl = generate_problem_pddl(&problem);
    Ok(pddl)
}

#[wasm_bindgen]
pub fn pdc_to_domain_and_problem_pddl(
    domain_code: &str,
    problem_code: &str,
) -> Result<String, JsValue> {
    let domain = parse_pdc(domain_code)
        .map_err(|e| JsValue::from_str(&format!("Domain parse error: {}", e)))?;

    let mut problem = parse_problem(problem_code)
        .map_err(|e| JsValue::from_str(&format!("Problem parse error: {}", e)))?;

    // Set the domain name from the parsed domain only if not already specified in the problem
    if problem.domain.is_empty() {
        problem.domain = domain.name.clone();
    }

    let (domain_pddl, problem_pddl) = generate_domain_and_problem_pddl(&domain, &problem);

    // Return both as a JSON-like structure for easy parsing in JavaScript
    Ok(format!(
        "{{\"domain\": {domain_pddl:?}, \"problem\": {problem_pddl:?}}}"
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pdc_to_pddl() {
        let pdc_code = r#"domain logistics {
    type Location, Truck, Quantity;

    predicate at(t: Truck, l: Location);
    predicate demand_ambient_goods(l: Location, d: Quantity);
    predicate free_capacity(t: Truck, c: Quantity);
    predicate plus1(x: Quantity, y: Quantity);
    predicate visited(l: Location);

    action deliver_ambient(t: Truck,
        l: Location,
        d: Quantity,
        d_less_one: Quantity,
        c: Quantity,
        c_less_one: Quantity
    )
        requires at(t, l) & demand_ambient_goods(l, d) & free_capacity(t, c)
        requires plus1(d_less_one, d) & plus1(c_less_one, c)
        ensures !(at(t, l)) & at(t, l)
        ensures visited(l);
}"#;

        let result = pdc_to_pddl(pdc_code);
        assert!(result.is_ok());
        println!("Generated PDDL:\n{}", result.unwrap());
    }

    #[test]
    fn test_parse_pdc_problem() {
        let problem_code = r#"problem mixed-f2-p1-u0-v0-g0-a0-n0-A0-B0-N0-F0-r1: elevator {
            let p0: Passenger;
            let f0: Floor, f1: Floor;

            init {
                above(f0, f1);
                origin(p0, f0);
                destin(p0, f1);
                lift-at(f0);
            }

            goal {
                served(p0);
            }
        }"#;

        let result = parse_pdc_problem(problem_code);
        assert!(result.is_ok());
        println!("{:?}", result);
        let parsed_output = result.unwrap();
        assert!(parsed_output.contains("mixed-f2-p1-u0-v0-g0-a0-n0-A0-B0-N0-F0-r1"));
        assert!(parsed_output.contains("Passenger"));
        assert!(parsed_output.contains("Floor"));
        println!("Parsed problem:\n{}", parsed_output);
    }

    #[test]
    fn test_problem_to_pddl() {
        let problem_code = r#"problem mixed-f2-p1-u0-v0-g0-a0-n0-A0-B0-N0-F0-r1: elevator {
            let p0: Passenger;
            let f0: Floor, f1: Floor;

            init {
                above(f0, f1);
                origin(p0, f0);
                destin(p0, f1);
                lift-at(f0);
            }

            goal {
                served(p0);
            }
        }"#;

        let result = problem_to_pddl(problem_code, "");
        assert!(result.is_ok());
        let pddl_output = result.unwrap();
        assert!(
            pddl_output.contains("(define (problem mixed-f2-p1-u0-v0-g0-a0-n0-A0-B0-N0-F0-r1)")
        );
        assert!(pddl_output.contains("(:domain elevator)"));
        assert!(pddl_output.contains("(:objects"));
        assert!(pddl_output.contains("(:init"));
        assert!(pddl_output.contains("(:goal"));
        println!("Generated problem PDDL:\n{}", pddl_output);
    }

    #[test]
    fn test_pdc_to_domain_and_problem_pddl() {
        let domain_code = r#"domain elevator {
            type Passenger, Floor;

            predicate lift-at(floor: Floor);
            predicate served(person: Passenger);
        }"#;

        let problem_code = r#"problem test-elevator: elevator {
            let p0: Passenger;
            let f0: Floor;

            init {
                lift-at(f0);
            }

            goal {
                served(p0);
            }
        }"#;

        let result = pdc_to_domain_and_problem_pddl(domain_code, problem_code);
        assert!(result.is_ok());
        let combined_output = result.unwrap();

        // Verify it contains both domain and problem
        assert!(combined_output.contains("domain"));
        assert!(combined_output.contains("problem"));
        assert!(combined_output.contains("elevator"));
        assert!(combined_output.contains("test-elevator"));

        println!("Combined domain and problem output:\n{}", combined_output);
    }

    #[test]
    fn test_complete_readme_example() {
        let domain_code = r#"domain elevator {
            type Passenger, Floor;

            predicate origin(person: Passenger, floor: Floor);
            predicate destin(person: Passenger, floor: Floor);
            predicate above(floor1: Floor, floor2: Floor);
            predicate boarded(person: Passenger);
            predicate not-boarded(person: Passenger);
            predicate served(person: Passenger);
            predicate not-served(person: Passenger);
            predicate lift-at(floor: Floor);

            action board(f: Floor, p: Passenger)
                requires lift-at(f)
                requires origin(p, f)
                ensures boarded(p);

            action depart(f: Floor, p: Passenger)
                requires lift-at(f)
                requires destin(p, f)
                requires boarded(p)
                ensures !(boarded(p)) & served(p);
        }"#;

        let problem_code = r#"problem mixed-f2-p1-u0-v0-g0-a0-n0-A0-B0-N0-F0-r1: elevator {
            let p0: Passenger;
            let f0: Floor, f1: Floor;

            init {
                above(f0, f1);
                origin(p0, f0);
                destin(p0, f1);
                lift-at(f0);
            }

            goal {
                served(p0);
            }
        }"#;

        // Test individual parsing
        let domain_result = parse_pdc(domain_code);
        assert!(domain_result.is_ok());
        let domain = domain_result.unwrap();
        assert_eq!(domain.name, "elevator");
        assert_eq!(domain.types.len(), 2);
        assert_eq!(domain.predicates.len(), 8);
        assert_eq!(domain.actions.len(), 2);

        let problem_result = parse_problem(problem_code);
        assert!(problem_result.is_ok());
        let problem = problem_result.unwrap();
        assert_eq!(problem.name, "mixed-f2-p1-u0-v0-g0-a0-n0-A0-B0-N0-F0-r1");
        assert_eq!(problem.domain, "elevator");
        assert_eq!(problem.variables.len(), 3);
        assert_eq!(problem.init.len(), 4);
        assert_eq!(problem.goal.len(), 1);

        // Test PDDL generation
        let domain_pddl = pdc_to_pddl(domain_code);
        assert!(domain_pddl.is_ok());
        let domain_output = domain_pddl.unwrap();
        assert!(domain_output.contains("(define (domain elevator)"));
        assert!(domain_output.contains("Passenger - object"));
        assert!(domain_output.contains("Floor - object"));
        assert!(domain_output.contains("(:action board"));
        assert!(domain_output.contains("(:action depart"));

        let problem_pddl = problem_to_pddl(problem_code, "");
        assert!(problem_pddl.is_ok());
        let problem_output = problem_pddl.unwrap();
        assert!(
            problem_output.contains("(define (problem mixed-f2-p1-u0-v0-g0-a0-n0-A0-B0-N0-F0-r1)")
        );
        assert!(problem_output.contains("(:domain elevator)"));
        assert!(problem_output.contains("p0 - passenger"));
        assert!(problem_output.contains("f0 f1 - floor"));
        assert!(problem_output.contains("(above f0 f1)"));
        assert!(problem_output.contains("(:goal (served p0))"));

        println!("Complete README example test passed!");
        println!("Domain PDDL:\n{}", domain_output);
        println!("Problem PDDL:\n{}", problem_output);
    }

    #[test]
    fn test_problem_without_domain_with_external_domain() {
        let problem_code = r#"problem test-problem-external-domain {
            let p0: Passenger;
            let f0: Floor;

            init {
                lift-at(f0);
                origin(p0, f0);
            }

            goal {
                served(p0);
            }
        }"#;

        // Test that problem_to_pddl uses the external domain name when problem doesn't specify one
        let result = problem_to_pddl(problem_code, "elevator");
        assert!(result.is_ok());
        let pddl_output = result.unwrap();

        assert!(pddl_output.contains("(define (problem test-problem-external-domain)"));
        assert!(pddl_output.contains("(:domain elevator)"));
        assert!(pddl_output.contains("p0 - passenger"));
        assert!(pddl_output.contains("f0 - floor"));
        assert!(pddl_output.contains("(lift-at f0)"));
        assert!(pddl_output.contains("(origin p0 f0)"));
        assert!(pddl_output.contains("(:goal (served p0))"));

        println!("Problem with external domain PDDL:\n{}", pddl_output);
    }
}
