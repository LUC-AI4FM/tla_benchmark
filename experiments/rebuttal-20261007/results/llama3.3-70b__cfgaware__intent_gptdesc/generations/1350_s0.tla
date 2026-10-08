---------------------------- MODULE CounterSpec ----------------------------
EXTENDS Integers

CONSTANT InitCounter
VARIABLE counter

Init == (counter = 1)

Next == (counter < 5) => (counter' = counter + 1) <> (counter' = counter)

Spec == Init /\ [][Next]_counter

Liveness == <>[]((counter = 5) /\ [](counter' = counter))

THEOREM Spec => []((counter >= 1) /\ (counter <= 5))
THEOREM Spec => <>[]((counter = 5) /\ [](counter' = counter)) => Liveness
=============================================================================