------------------------------ MODULE Barrier ------------------------------
EXTENDS Naturals, TLC

CONSTANTS N, Proc
(* Assume Proc is a finite nonempty set of process identifiers and |Proc| = N *)

VARIABLES phase, round

Phase == {"idle", "arrived"}

vars == <<phase, round>>

Init ==
  /\ phase \in [Proc -> Phase]
  /\ phase = [p ∈ Proc |-> "idle"]
  /\ round = 0

Arrive(p) ==
  /\ p ∈ Proc
  /\ phase[p] = "idle"
  /\ phase' = [phase EXCEPT ![p] = "arrived"]

Release ==
  /\ \A p ∈ Proc : phase[p] = "arrived"
  /\ phase' = [p ∈ Proc |-> "idle"]
  /\ round' = round + 1

Next == 
  (\E p ∈ Proc : Arrive(p)) \/ Release

TypeInv ==
  /\ phase \in [Proc -> Phase]
  /\ round \in Nat
  /\ \A p ∈ Proc : phase[p] = "idle" \/ phase[p] = "arrived"

Assumptions ==
  /\ Proc \subseteq Nat
  /\ N > 0
  /\ |Proc| = N

Spec == Init /\ [][Next]_vars /\ TypeInv /\ Assumptions

Liveness ==
  WF_∃(Release) /\ \A p ∈ Proc : WF_∃(Arrive(p))

=============================================================================