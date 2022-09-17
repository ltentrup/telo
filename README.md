# telo - Specifying temporal properties in Rust

With telo, you can specify temporal properties using [linear-time temporal logic (LTL)](https://en.wikipedia.org/wiki/Linear_temporal_logic).
Those specifications can be transformed into monitoring automata, which can detect violations of safety specifications during runtime.


## How-to: Runtime monitoring

```rust
use telo::{*, predicate::*, monitor::*};

// Step 1: define predicates
const LIMIT: i32 = 123;

let mut builder = Predicates::builder();
let above_limit = builder.new_predicate(ClosurePredicate::new(
    |val: &i32| *val >= LIMIT,
     "value is above LIMIT",
));
let predicates = builder.build();

// Step 2: define temporal specification
let property = Property::never(Property::atomic(above_limit));

// Step 3: monitoring automaton
let automaton = property.to_monitoring_automaton(&predicates);

// Step 4: Runtime monitoring
let mut monitor = Monitor::new(predicates, automaton);
for value in 0..LIMIT {
  assert!(monitor.next_state(&value));
}
assert!(!monitor.next_state(&LIMIT)); // the property is violated
```

## From LTL to minimal and deterministic safety automata

* LTL over an arbitrary domain using self-defined predicates
* Translation to LTL in negation normal form
* Translation to alternating-time Büchi automaton
* Translation to non-deterministic Büchi automaton (via Miyano-Hayashi construction)
* Re-interpretation as non-deterministic safety automaton
* Determinize and minimize safety automaton

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.