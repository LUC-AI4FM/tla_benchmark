```
MODULE J
EXTENDS Integers

CONSTANTS 
VARIABLES x, y

Init == (x \in {1, 2, 3, 4, 5}) /\ (y = [i \in {1, 2, 3, 4, 5} |-> 0])

Foo(y) == IF x = 1 THEN [y EXCEPT ![1] = 42] ELSE y

Next == y' = Foo(y)

Spec == Init /\ [][Next]_<<x, y>>
```