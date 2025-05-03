use nom::{
    IResult,
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1, multispace0, multispace1},
    combinator::{map, opt, recognize},
    multi::{many0, many1, separated_list0, separated_list1},
    sequence::{delimited, pair, preceded},
    Parser,
};
use std::fmt;

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

// Parser functions
fn parse_identifier(input: &str) -> IResult<&str, String> {
    map(
        recognize(pair(
            alt((alpha1, tag("_"), tag("-"))),
            many0(alt((alphanumeric1, tag("_"), tag("-")))),
        )),
        |s: &str| s.to_string(),
    ).parse(input)
}

fn parse_parameter(input: &str) -> IResult<&str, Parameter> {
    let (input, _) = multispace0(input)?;
    let (input, name) = parse_identifier(input)?;
    let (input, _) = multispace0(input)?;
    let (input, data_type) = opt(preceded(
        delimited(multispace0, tag(":"), multispace0),
        parse_identifier,
    )).parse(input)?;
    let (input, _) = multispace0(input)?;
    Ok((input, Parameter { name, data_type }))
}

fn parse_predicate(input: &str) -> IResult<&str, Predicate> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("predicate")(input)?;
    let (input, _) = multispace1(input)?;
    let (input, name) = parse_identifier(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, parameters) = separated_list0(
        delimited(multispace0, tag(","), multispace0),
        parse_parameter,
    ).parse(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(")")(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(";")(input)?;
    Ok((input, Predicate { name, parameters }))
}

fn parse_call(input: &str) -> IResult<&str, Value> {
    let (input, _) = multispace0(input)?;
    let (input, name) = parse_identifier(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, args) = separated_list0(
        delimited(multispace0, tag(","), multispace0),
        parse_identifier,
    ).parse(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(")")(input)?;
    Ok((input, Value::Call(name, args)))
}

fn parse_parenthesized_value(input: &str) -> IResult<&str, Value> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, value) = parse_value(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(")")(input)?;
    Ok((input, value))
}

fn parse_atomic_value(input: &str) -> IResult<&str, Value> {
    let (input, _) = multispace0(input)?;
    alt((
        parse_not,
        parse_call,
        parse_parenthesized_value,
    )).parse(input)
}

fn parse_not(input: &str) -> IResult<&str, Value> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("!")(input)?;
    let (input, value) = alt((
        parse_call,
        parse_parenthesized_value,
    )).parse(input)?;
    Ok((input, Value::Not(Box::new(value))))
}

fn flatten_and(value: Value) -> Value {
    match value {
        Value::And(values) => {
            let mut flattened = Vec::new();
            for v in values {
                match flatten_and(v) {
                    Value::And(more_values) => flattened.extend(more_values),
                    v => flattened.push(v),
                }
            }
            Value::And(flattened)
        }
        Value::Or(values) => {
            Value::Or(values.into_iter().map(flatten_and).collect())
        }
        Value::Not(boxed) => Value::Not(Box::new(flatten_and(*boxed))),
        v => v,
    }
}

fn flatten_or(value: Value) -> Value {
    match value {
        Value::Or(values) => {
            let mut flattened = Vec::new();
            for v in values {
                match flatten_or(v) {
                    Value::Or(more_values) => flattened.extend(more_values),
                    v => flattened.push(v),
                }
            }
            Value::Or(flattened)
        }
        Value::And(values) => {
            Value::And(values.into_iter().map(flatten_or).collect())
        }
        Value::Not(boxed) => Value::Not(Box::new(flatten_or(*boxed))),
        v => v,
    }
}

fn parse_and(input: &str) -> IResult<&str, Value> {
    let (input, first) = parse_atomic_value(input)?;
    let (input, rest) = many0(preceded(
        delimited(multispace0, tag("&"), multispace0),
        parse_atomic_value,
    )).parse(input)?;
    
    if rest.is_empty() {
        Ok((input, first))
    } else {
        let mut values = vec![first];
        values.extend(rest);
        Ok((input, flatten_and(Value::And(values))))
    }
}

fn parse_or(input: &str) -> IResult<&str, Value> {
    let (input, first) = parse_and(input)?;
    let (input, rest) = many0(preceded(
        delimited(multispace0, tag("|"), multispace0),
        parse_and,
    )).parse(input)?;
    
    if rest.is_empty() {
        Ok((input, first))
    } else {
        let mut values = vec![first];
        values.extend(rest);
        Ok((input, flatten_or(Value::Or(values))))
    }
}

fn parse_value(input: &str) -> IResult<&str, Value> {
    let (input, _) = multispace0(input)?;
    parse_or(input)
}

fn parse_action(input: &str) -> IResult<&str, Action> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("action")(input)?;
    let (input, _) = multispace1(input)?;
    let (input, name) = parse_identifier(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, parameters) = separated_list0(
        delimited(multispace0, tag(","), multispace0),
        delimited(multispace0, parse_parameter, multispace0),
    ).parse(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(")")(input)?;
    let (input, _) = multispace0(input)?;
    
    let mut input = input;
    let mut preconditions = Vec::new();
    let mut effects = Vec::new();
    
    loop {
        let (new_input, _) = multispace0(input)?;
        input = new_input;
        
        if let Ok((new_input, _)) = tag::<&str, &str, nom::error::Error<&str>>("requires")(input) {
            let (new_input, _) = multispace0(new_input)?;
            let (new_input, conditions) = many1(delimited(
                multispace0,
                parse_value,
                preceded(
                    opt(delimited(multispace0, tag("&"), multispace0)),
                    multispace0,
                ),
            )).parse(new_input)?;
            preconditions.extend(conditions);
            input = new_input;
            continue;
        }
        
        if let Ok((new_input, _)) = tag::<&str, &str, nom::error::Error<&str>>("ensures")(input) {
            let (new_input, _) = multispace0(new_input)?;
            let (new_input, conditions) = many1(delimited(
                multispace0,
                parse_value,
                preceded(
                    opt(delimited(multispace0, tag("&"), multispace0)),
                    multispace0,
                ),
            )).parse(new_input)?;
            effects.extend(conditions);
            input = new_input;
            continue;
        }
        
        break;
    }
    
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(";")(input)?;
    
    // Merge all preconditions and effects into single And structures
    let preconditions = if preconditions.is_empty() {
        Vec::new()
    } else {
        vec![Value::And(preconditions)]
    };
    
    let effects = if effects.is_empty() {
        Vec::new()
    } else {
        vec![Value::And(effects)]
    };
    
    // Flatten nested And structures
    let preconditions = preconditions.into_iter().map(flatten_and).collect();
    let effects = effects.into_iter().map(flatten_and).collect();
    
    Ok((input, Action {
        name,
        parameters,
        preconditions,
        effects,
    }))
}

fn parse_single_type(input: &str) -> IResult<&str, (String, Option<String>)> {
    let (input, _) = multispace0(input)?;
    let (input, name) = parse_identifier(input)?;
    let (input, _) = multispace0(input)?;
    let (input, parent) = opt(preceded(
        tag(":"),
        preceded(multispace0, parse_identifier),
    )).parse(input)?;
    let (input, _) = multispace0(input)?;
    Ok((input, (name, parent)))
}

fn parse_type_decl(input: &str) -> IResult<&str, Vec<(String, Option<String>)>> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("type")(input)?;
    let (input, _) = multispace1(input)?;
    let (input, types) = separated_list1(
        tag(","),
        parse_single_type,
    ).parse(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag(";")(input)?;
    Ok((input, types))
}

fn parse_domain(input: &str) -> IResult<&str, Domain> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("domain")(input)?;
    let (input, _) = multispace1(input)?;
    let (input, name) = parse_identifier(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("{")(input)?;
    let (input, _) = multispace0(input)?;
    
    let mut input = input;
    let mut types = Vec::new();
    let mut predicates = Vec::new();
    let mut actions = Vec::new();
    
    loop {
        let (new_input, _) = multispace0(input)?;
        input = new_input;
        
        if let Ok((new_input, type_decls)) = parse_type_decl(input) {
            types.extend(type_decls);
            input = new_input;
            continue;
        }
        
        if let Ok((new_input, predicate)) = parse_predicate(input) {
            predicates.push(predicate);
            input = new_input;
            continue;
        }
        
        if let Ok((new_input, action)) = parse_action(input) {
            actions.push(action);
            input = new_input;
            continue;
        }
        
        break;
    }
    
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("}")(input)?;
    
    Ok((input, Domain {
        name,
        types,
        predicates,
        actions,
    }))
}

pub fn parse_pdc(input: &str) -> Result<Domain, String> {
    parse_domain(input)
        .map(|(_, domain)| {
            domain
        })
        .map_err(|e| format!("Parse error: {:?}", e))
} 

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_action() {
        // Test basic action with simple conditions
        let pdc_code = r#"action deliver_ambient(t: Truck, 
        l: Location, 
        d: Quantity, 
        d_less_one: Quantity,
        c: Quantity, 
        c_less_one: Quantity
    ) 
        requires at(t, l) & demand_ambient_goods(l, d) & free_capacity(t, c)
        requires plus1(d_less_one, d) & plus1(c_less_one, c)
        ensures !(at(t, l)) & at(t, l)
        ensures visited(l);"#;
        let (_, action) = parse_action(pdc_code).unwrap();
        println!("Parsed action: {:?}", action);

        // Test with more complex conditions
        let complex_pdc = r#"action complex_action(x: Type, y: Type)
            requires (at(x, y) | !at(y, x)) & (has(x) | !has(y))
            ensures !(at(x, y)) & (visited(x) | visited(y));"#;
        let (_, complex_action) = parse_action(complex_pdc).unwrap();
        println!("Parsed complex action: {:?}", complex_action);

        // Test individual value parsers
        let call_expr = "at(t, l)";
        let (_, call_value) = parse_value(call_expr).unwrap();
        println!("Parsed call: {:?}", call_value);

        let not_expr = "!(at(t, l))";
        let (_, not_value) = parse_value(not_expr).unwrap();
        println!("Parsed not: {:?}", not_value);

        let and_expr = "at(t, l) & demand_ambient_goods(l, d)";
        let (_, and_value) = parse_value(and_expr).unwrap();
        println!("Parsed and: {:?}", and_value);

        let or_expr = "at(t, l) | !demand_ambient_goods(l, d)";
        let (_, or_value) = parse_value(or_expr).unwrap();
        println!("Parsed or: {:?}", or_value);
    }

    #[test]
    fn test_flattening() {
        // Test merging of multiple requires and ensures
        let action_code = r#"action test_action(x: Type)
            requires at(x, y)
            requires visited(x)
            ensures !(at(x, y))
            ensures visited(y);"#;
        let (_, action) = parse_action(action_code).unwrap();
        println!("Parsed action: {:?}", action);
        
        // Verify preconditions are merged into a single And
        assert_eq!(action.preconditions.len(), 1);
        match &action.preconditions[0] {
            Value::And(values) => {
                assert_eq!(values.len(), 2);
                assert!(matches!(values[0], Value::Call(_, _)));
                assert!(matches!(values[1], Value::Call(_, _)));
            }
            _ => panic!("Expected And value for preconditions"),
        }
        
        // Verify effects are merged into a single And
        assert_eq!(action.effects.len(), 1);
        match &action.effects[0] {
            Value::And(values) => {
                assert_eq!(values.len(), 2);
                assert!(matches!(values[0], Value::Not(_)));
                assert!(matches!(values[1], Value::Call(_, _)));
            }
            _ => panic!("Expected And value for effects"),
        }
    }

    #[test]
    fn test_generate_pddl_part_2() {
        let pdc_code = r#" action deliver_ambient(t: Truck, 
        l: Location, 
        d: Quantity, 
        d_less_one: Quantity,
        c: Quantity, 
        c_less_one: Quantity
    ) 
        requires at(t, l) & demand_ambient_goods(l, d) & free_capacity(t, c)
        requires plus1(d_less_one, d) & plus1(c_less_one, c)
        ensures !(at(t, l)) & at(t, l)
        ensures visited(l);"#;
        let (_, action) = parse_action(pdc_code).unwrap();
        println!("{:?}", action.effects);
        // assert_eq!(true, false);
    }
}
