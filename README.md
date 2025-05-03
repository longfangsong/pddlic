# PDDLIC

PDDL, but in C like syntax.

Because I am not a big fan of Lisp.

The syntax are borrowed from Rust(type) and Dafny(requires/ensures).

Try it ![here](https://longfangsong.github.io/pddlic/).

## Features

- [x] domain
- [ ] problem
- [x] type
- [x] predicate
- [x] action
- [ ] function
- [ ] import
- [ ] ... 

## Example

```rust
domain gripper-strips {
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

    action up(f1: Floor, f2: Floor)
        requires lift-at(f)
        requires above(f1, f2)
        ensures lift-at(f2)
        ensures !(lift-at(f1));

    action down(f1: Floor, f2: Floor)
        requires lift-at(f)
        requires above(f2, f1)
        ensures lift-at(f2)
        ensures !(lift-at(f1));
}
```
Will become

```pddl
(define (domain gripper-strips)
  (:requirements :strips :typing)
  (:types
    Passenger - object
    Floor - object
  )
  (:predicates
    (origin ?person - Passenger ?floor - Floor)
    (destin ?person - Passenger ?floor - Floor)
    (above ?floor1 - Floor ?floor2 - Floor)
    (boarded ?person - Passenger)
    (not-boarded ?person - Passenger)
    (served ?person - Passenger)
    (not-served ?person - Passenger)
    (lift-at ?floor - Floor)
  )
  (:action board
  :parameters (?f - Floor ?p - Passenger)
  :precondition (and (lift-at ?f) (origin ?p ?f))
  :effect (and (boarded ?p))
)
  (:action depart
  :parameters (?f - Floor ?p - Passenger)
  :precondition (and (lift-at ?f) (destin ?p ?f) (boarded ?p))
  :effect (and (not (boarded ?p)) (served ?p))
)
  (:action up
  :parameters (?f1 - Floor ?f2 - Floor)
  :precondition (and (lift-at ?f) (above ?f1 ?f2))
  :effect (and (lift-at ?f2) (not (lift-at ?f1)))
)
  (:action down
  :parameters (?f1 - Floor ?f2 - Floor)
  :precondition (and (lift-at ?f) (above ?f2 ?f1))
  :effect (and (lift-at ?f2) (not (lift-at ?f1)))
)
)
```
