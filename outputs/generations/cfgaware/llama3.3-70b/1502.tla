```
MODULE SmallStateMachine
VARIABLE x

Op == [x \in Nat |-> {x + 1, x - 1, x}]

Forty2 == 42

Init ==
  x = 0

Next ==
  x' \in Op(x)

SUBSET_Self(x) ==
  {x}

SUBSET_Op(x) ==
  Op(x)
```
Note: The `Nat` set is assumed to be defined elsewhere, possibly in the `Integers` or `Naturals` module. If not, you can define it as a constant set of natural numbers within this module. 

Also note that the `SUBSET_Self` and `SUBSET_Op` operators seem redundant given their simple definitions, but they are included to fulfill the requirement of defining exactly the named constants, variables, and operators listed.