------------------------------- MODULE MultiSlotConsensus -------------------------------
(***************************************************************************)
(* An abstract multi-slot consensus model.  Values may first be proposed  *)
(* and then, independently for each slot, a proposed value may be chosen. *)
(* There is no fault model: no crashes and no Byzantine behaviour.        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Value, Slots

ASSUME ValueAssump == /\ Value # {}
                      /\ IsFiniteSet(Value)
ASSUME SlotsAssump == IsFiniteSet(Slots)

(***************************************************************************
--algorithm MultiSlotConsensus {
  variables chosen = [s \in Slots |-> {}],
            proposed = {};
  {
    lbl: while (TRUE) {
           either {
             with (v \in Value \ proposed) {
               proposed := proposed \cup {v}
             }
           }
           or {
             with (s \in {sl \in Slots : chosen[sl] = {}}, v \in proposed) {
               chosen[s] := {v}
             }
           }
         }
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES chosen, proposed

vars == << chosen, proposed >>

Init == /\ chosen = [s \in Slots |-> {}]
        /\ proposed = {}

Propose == /\ \E v \in Value \ proposed :
                proposed' = proposed \cup {v}
           /\ UNCHANGED chosen

Choose == /\ \E s \in {sl \in Slots : chosen[sl] = {}} :
               \E v \in proposed :
                  chosen' = [chosen EXCEPT ![s] = {v}]
          /\ UNCHANGED proposed

Next == Propose \/ Choose

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)
\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == /\ proposed \subseteq Value
          /\ chosen \in [Slots -> SUBSET Value]

\* Only proposed values may be chosen.
Nontriviality == \A s \in Slots : chosen[s] \subseteq proposed

\* At most one value is chosen per slot.
Consistency == \A s \in Slots : Cardinality(chosen[s]) <= 1

Inv == TypeOK /\ Nontriviality /\ Consistency

\* Once a value is chosen for a slot, it stays chosen.
StabilityStep == \A s \in Slots : chosen[s] # {} => chosen'[s] = chosen[s]
Stability == [][StabilityStep]_vars

(* Liveness property *)

EventuallyAllChosen == <>(\A s \in Slots : chosen[s] # {})

-----------------------------------------------------------------------------
THEOREM TypeCorrect     == Spec => []TypeOK
THEOREM NontrivialThm   == Spec => []Nontriviality
THEOREM ConsistentThm   == Spec => []Consistency
THEOREM StableThm       == Spec => Stability
THEOREM LivenessThm     == FairSpec => EventuallyAllChosen
=============================================================================