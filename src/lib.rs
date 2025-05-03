pub mod pdc;
pub mod pddl;

use wasm_bindgen::prelude::*;
use pdc::parse_pdc;
use pddl::generate_pddl;

#[wasm_bindgen]
pub fn pdc_to_pddl(pdc_code: &str) -> Result<String, JsValue> {
    let domain = parse_pdc(pdc_code)
        .map_err(|e| JsValue::from_str(&format!("Parse error: {}", e)))?;
    
    let pddl = generate_pddl(&domain);
    Ok(pddl)
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
}
