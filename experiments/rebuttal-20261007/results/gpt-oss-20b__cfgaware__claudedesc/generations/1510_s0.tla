------------------------------ MODULE J ------------------------------
VARIABLES x, y

Init == /\ x \in {1,2,3,4,5}
        /\ y = [i \in 1..5 |-> 0]

Foo(xVal, f) ==
    IF xVal = 1 THEN
        [f EXCEPT ![xVal] = 42]
    ELSE
        f

Next == /\ UNCHANGED x
        /\ y' = Foo(x, y)

Stutter(action) == action \/ UNCHANGED <<x,y>>

Spec == Init /\ []Stutter(Next)
=============================================================================