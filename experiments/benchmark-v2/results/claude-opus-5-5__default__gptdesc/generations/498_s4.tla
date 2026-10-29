------------------------------- MODULE MultiSlotConsensus -------------------------------
(***************************************************************************)
(* An abstract multi-slot consensus model.  Values may first be proposed  *)
(* and then, independently for every slot, a proposed value may be       *)
(* chosen for a slot whose chosen set is still empty.  There are no      *)
(* faults: no crashes, message loss, or Byzantine behavior.  The model is *)
(* purely nondeterministic.                                               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Value,   \* the set of values that may be proposed
          Slot     \* the set of consensus slots (instances)

ASSUME ValueAssump == IsFiniteSet(Value) /\ Value # {}
ASSUME SlotAssump  == IsFiniteSet(Slot)

(***************************************************************************
--algorithm MultiSlotConsensus
{
  variables proposed = {},
            chosen   = [s \in Slot |-> {}];
  {
    either
      { with (v \in Value \ proposed)
          proposed := proposed \cup {v} }
    or
      { with (s \in {t \in Slot : chosen[t] = {}}, v \in proposed)
          chosen[s] := {v} }
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES proposed, chosen

vars == << proposed, chosen >>

Init == /\ proposed = {}
        /\ chosen = [s \in Slot |-> {}]

Propose == \E v \in Value \ proposed :
              /\ proposed' = proposed \cup {v}
              /\ UNCHANGED chosen

Choose == \E s \in {t \in Slot : chosen[t] = {}} :
            \E v \in proposed :
              /\ chosen' = [chosen EXCEPT ![s] = {v}]
              /\ UNCHANGED proposed

Next == Propose \/ Choose

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                      *)
(***************************************************************************)
TypeOK == /\ proposed \subseteq Value
          /\ chosen \in [Slot -> SUBSET Value]

\* Only proposed values may be chosen.
Nontriviality == \A s \in Slot : chosen[s] \subseteq proposed

\* At most one value is chosen per slot.
Consistency == \A s \in Slot : Cardinality(chosen[s]) <= 1

\* Once a value is chosen for a slot, it never changes.
Stability == [][\A s \in Slot : chosen[s] # {} => chosen'[s] = chosen[s]]_vars

\* Proposed values are never retracted.
ProposedStable == [][proposed \subseteq proposed']_vars

Inv == TypeOK /\ Nontriviality /\ Consistency

(***************************************************************************)
(* Liveness: eventually every slot has a chosen value.                    *)
(***************************************************************************)
Liveness == <>(\A s \in Slot : chosen[s] # {})

THEOREM TypeCorrect      == Spec => []TypeOK
THEOREM NontrivialityThm == Spec => []Nontriviality
THEOREM ConsistencyThm   == Spec => []Consistency
THEOREM StabilityThm     == Spec => Stability
THEOREM LivenessThm      == Spec => Liveness
=============================================================================