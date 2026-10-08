------------------------------ MODULE SingleVarInit ------------------------------
EXTENDS Naturals, TLC

VARIABLE s

(* Initialization predicate for a variable *)
Init(var) == \E v \in 0..1 : (var = v) /\ (v < 1)

(* State invariant *)
Inv == s < 1

(* Initial condition: s satisfies Init *)
InitCond == Init(s)

(* Next action: s remains unchanged *)
Next == UNCHANGED <<s>>

Spec == InitCond /\ [] [ Next ]_<<s>>

(* Safety invariant explicitly stated *)
SafetyInvariant == [] Inv
=============================================================================