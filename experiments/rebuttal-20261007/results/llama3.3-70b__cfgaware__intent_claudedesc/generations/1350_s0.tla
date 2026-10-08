---------------------------- MODULE CounterSpec ----------------------------
EXTENDS Integers

CONSTANT MaxValue
VARIABLE counter

Init == (counter = 1)

Next == (counter < MaxValue) => (counter' = counter + 1) <> (counter' = counter)

Spec == Init /\ [][Next]_counter
       /\ WF_vars(Next, counter)

Liveness == counter = 1 ~> (counter = MaxValue /\ counter' = counter)
=============================================================================