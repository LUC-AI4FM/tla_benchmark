MODULE RecursionDemo
EXTENDS Naturals

CONSTANT N

VARIABLES x

RecFun == [n \in 0..N |-> IF n = 0 THEN 0 ELSE IF n = 1 THEN 1 ELSE RecFun[n-1] + RecFun[n-2]]

RangeSet == { RecFun[i] : i \in 0..N }

Init == /\ x \in RangeSet

Next == (x' = x)

Spec == Init /\ [][Next]_<<x>>

Inv == x \in RangeSet
Safety == []Inv

===============================================================================