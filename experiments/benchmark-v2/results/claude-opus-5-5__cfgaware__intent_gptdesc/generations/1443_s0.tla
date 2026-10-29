---------------------------- MODULE CyclicCounter ----------------------------
EXTENDS Naturals

VARIABLE count

vars == <<count>>

States == {0, 1, 2}

Init == count = 0

Next == count' = (count + 1) % 3

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety: the state is always one of 0, 1 or 2. *)
PossibleCounts == count \in States

(* Determinism: every step has exactly one successor. *)
Successor(s) == (s + 1) % 3

Deterministic ==
    [][ /\ count \in States
        /\ count' = Successor(count)
        /\ \A t \in States : (t = count') <=> (t = Successor(count)) ]_vars

(* Reachability: state 1 is reached. *)
AtOne == <>(count = 1)

(* Reachability: state 2 is reached. *)
AtTwo == <>(count = 2)

(* Wrap-around: the step from 2 back to 0 happens at least once. *)
WrapAround == <><<count = 2 /\ count' = 0>>_vars

(* Every state is reached, and the counter wraps around. *)
AllDone == AtOne /\ AtTwo /\ WrapAround

(* Cycle liveness: all three states are visited infinitely often. *)
_POSSIBLE ==
    /\ []<>(count = 0)
    /\ []<>(count = 1)
    /\ []<>(count = 2)

=============================================================================