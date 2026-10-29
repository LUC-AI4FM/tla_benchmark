---------------------------- MODULE MultiSlotConsensus ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Value, Slot

ASSUME ValueNonEmpty == Value # {}

(***************************************************************************
--algorithm MultiSlotConsensus {
  variables proposed = {},
            chosen = [s \in Slot |-> {}];
  {
    lbl: while (TRUE) {
           either {
             with (v \in Value \ proposed) {
               proposed := proposed \cup {v}
             }
           }
           or {
             with (s \in {sl \in Slot : chosen[sl] = {}}, v \in proposed) {
               chosen[s] := {v}
             }
           }
         }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES proposed, chosen

vars == << proposed, chosen >>

Init == /\ proposed = {}
        /\ chosen = [s \in Slot |-> {}]

Propose == /\ \E v \in Value \ proposed :
                 proposed' = proposed \cup {v}
           /\ UNCHANGED chosen

Choose == /\ \E s \in {sl \in Slot : chosen[sl] = {}} :
                \E v \in proposed :
                   chosen' = [chosen EXCEPT ![s] = {v}]
          /\ UNCHANGED proposed

Next == Propose \/ Choose

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Next)
\* END TRANSLATION
-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == /\ proposed \subseteq Value
          /\ chosen \in [Slot -> SUBSET Value]

\* Only proposed values may be chosen
Nontriviality == \A s \in Slot : chosen[s] \subseteq proposed

\* At most one value is chosen per slot
Consistency == \A s \in Slot : Cardinality(chosen[s]) <= 1

Inv == /\ TypeOK
       /\ Nontriviality
       /\ \A s \in Slot : chosen[s] = {} \/ \E v \in Value : chosen[s] = {v}

\* Once a value is chosen for a slot, it never changes
StabilityAction == \A s \in Slot : chosen[s] # {} => chosen'[s] = chosen[s]

Stability == [][StabilityAction]_vars

\* Proposed values are never retracted
ProposedStable == [][proposed \subseteq proposed']_vars

(* Liveness property *)

AllSlotsChosen == \A s \in Slot : chosen[s] # {}

Liveness == <>AllSlotsChosen

-----------------------------------------------------------------------------
THEOREM TypeCorrect == Spec => []TypeOK
THEOREM SafetyNontriviality == Spec => []Nontriviality
THEOREM SafetyConsistency == Spec => []Consistency
THEOREM SafetyInvariant == Spec => []Inv
THEOREM SafetyStability == Spec => Stability
THEOREM LivenessThm == Spec => Liveness
=============================================================================