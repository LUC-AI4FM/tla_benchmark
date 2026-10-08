------------------------------ MODULE SimpleCounter ------------------------------
EXTENDS Naturals

CONSTANTS
    ConstVal,
    MaxCounter

VARIABLES
    counter,
    stableVar

(* Domain of the stable component *)
StableDomain == {TRUE, FALSE}

(* Initial state predicate *)
Init ==
    /\ counter \in 0..MaxCounter
    /\ stableVar \in StableDomain

(* Increment action: increments counter while leaving stableVar unchanged *)
Increment ==
    /\ counter < MaxCounter
    /\ counter' = counter + 1
    /\ stableVar' = stableVar

(* Final state: no more increments allowed; system stays in place *)
FinalState ==
    /\ counter = MaxCounter
    /\ UNCHANGED <<counter, stableVar>>

Next == Increment \/ FinalState

Spec == Init /\ [][Next]_<<counter, stableVar>>

(* Invariant that all components stay within their domains *)
Invariant ==
    /\ counter \in 0..MaxCounter
    /\ stableVar \in StableDomain

(* Safety property: stableVar never changes while increment is enabled *)
Safety ==
    [] (counter < MaxCounter => stableVar' = stableVar)

(* Progress property: increment action eventually occurs until termination *)
Progress ==
    [] (counter < MaxCounter => <> Increment)

(* Liveness property: from any state where guard holds, eventually a state with incremented value is reached *)
Liveness ==
    [] (counter < MaxCounter => <> (counter' = counter + 1))

============================================================================