--------------------------- MODULE MultiSlotConsensus ---------------------------
EXTENDS Naturals, TLC

CONSTANTS SLOTS, VALUES

VARIABLES proposed, chosen

(* --- Types and Invariants ------------------------------------------------- *)
TypeOK == 
    /\ proposed ∈ SUBSET VALUES
    /\ chosen ∈ [SLOTS -> SUBSET VALUES]
    /\ \A s ∈ SLOTS : chosen[s] ⊆ VALUES

Consistency == \A s ∈ SLOTS : chosen[s] ⊆ proposed

(* --- Initial State -------------------------------------------------------- *)
Init == 
    /\ proposed = {}
    /\ chosen = [s \in SLOTS |-> {}]

(* --- Actions -------------------------------------------------------------- *)
Propose(v) ==
    /\ v ∈ VALUES
    /\ v ∉ proposed
    /\ proposed' = proposed ∪ {v}
    /\ UNCHANGED <<chosen>>

Pick(s, v) ==
    /\ s ∈ SLOTS
    /\ chosen[s] = {}
    /\ v ∈ proposed
    /\ chosen' = [chosen EXCEPT ![s] = {v}]
    /\ UNCHANGED <<proposed>>

Next == 
    \E v \in VALUES : Propose(v)
 \/ \E s \in SLOTS, v \in proposed : Pick(s, v)

(* --- Liveness ------------------------------------------------------------- *)
Liveness == \A s ∈ SLOTS : ◇ (chosen[s] ≠ {})

(* --- Specification -------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ Liveness

=============================================================================