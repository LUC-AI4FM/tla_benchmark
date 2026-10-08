```tla
MODULE SmallStateMachine

EXTENDS Integers, FiniteSets, TLC

CONSTANTS Domain
VARIABLES x, y

Init == /\ x \in 1..5
        /\ y = [d \in Domain |-> 0]

Foo(f, key) ==
    IF key = 1 THEN f[key] := 42 ELSE f[key] := f[key]

Next == /\ UNCHANGED x
        /\ y' = Foo(y, x)

Spec == Init /\ [][Next]_<<x,y>>
```