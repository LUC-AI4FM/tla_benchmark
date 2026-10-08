---- MODULE CounterFactorial ----
EXTENDS Integers

CONSTANTS SmallInput, LargeInput

ASSUME /\ SmallInput = 3
       /\ LargeInput = 9

VARIABLES counter

FACT_SMALL == 3 * 2 * 1
FACT_LARGE == 9 * 8 * 7 * 6 * 5 * 4 * 3 * 2 * 1

AllowedVals == {FACT_SMALL, FACT_LARGE}

Init == counter = 0

Short == counter' = FACT_SMALL
Long  == counter' = FACT_LARGE

Next == Short \/ Long

vars == << counter >>

Spec == Init /\ [][Next]_vars

(*
 Safety invariants
*)
TypeInv == counter \in Int
AllowedStateInv == counter = 0 \/ counter \in AllowedVals
ExactlyOneUpdate == [] (Next => (counter' \in AllowedVals) /\ ~((counter' = FACT_SMALL) /\ (counter' = FACT_LARGE)))

(*
 Liveness properties
*)
NonDeadlock == [] Enabled(Next)
PerpetualChoice == []<>(Enabled(Short)) /\ []<>(Enabled(Long))

====