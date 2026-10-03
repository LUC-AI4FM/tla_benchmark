```
MODULE SmallStateMachine
VARIABLE x

MyNat == 0..30

TypeOK == x \in MyNat

Init == x = 0

A == x' = x + 1

BandC == (x > 10) /\ (x' = x - 2)

DandE == (x < 20) /\ (x' = x + 3)

Next == A \/ BandC \/ DandE

Inv == x \in MyNat

Spec == []<>(Inv /\ [][Next]_x)
```
Note: The `[]<>` operator is not typically used with an invariant-like predicate. Instead, the `[]` operator (always) or `<>` operator (eventually) would be used separately. However, based on your request to define exactly the named constants, variables, and operators listed, I have included it as specified.

Also note that this specification may not be suitable for model checking due to the use of `_x` in the `[Next]_x` formula, which is typically used with a specific variable or tuple of variables. In this case, `x` should be sufficient. 

Here's an updated version:
```
MODULE SmallStateMachine
VARIABLE x

MyNat == 0..30

TypeOK == x \in MyNat

Init == x = 0

A == x' = x + 1

BandC == (x > 10) /\ (x' = x - 2)

DandE == (x < 20) /\ (x' = x + 3)

Next == A \/ BandC \/ DandE

Inv == x \in MyNat

Spec == Inv /\ []([Next]_x)
```