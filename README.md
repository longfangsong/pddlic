# PDDLIC

PDDL, but in C like syntax.

Because I am not a big fan of Lisp.

The syntax are borrowed from Rust(type) and Dafny(requires/ensures).

Try it ![here](https://longfangsong.github.io/pddlic/).

## Features

- [x] domain
- [x] problem
- [x] type
- [x] predicate
- [x] action
- [ ] function
- [ ] import
- [ ] ...

## Example

```rust
domain elevator {
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

problem mixed-f2-p1-u0-v0-g0-a0-n0-A0-B0-N0-F0-r1: elevator {
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
}
```

Will become

```pddl
; domain.pddl
(define (domain miconic)
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

```pddl
; problem.pddl

(define (problem mixed-f2-p1-u0-v0-g0-a0-n0-A0-B0-N0-F0-r1)
  (:domain miconic)
  (:objects p0    - passenger
            f0 f1 - floor)

  (:init
    (above f0 f1)
    (origin p0 f0)
    (destin p0 f1)
    (lift-at f0)
  )

  (:goal (served p0))
)
```
