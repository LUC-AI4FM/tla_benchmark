---------------------------- MODULE MultiSlotConsensus ----------------------------
(***************************************************************************)
(* An abstract multi-slot consensus model. Values are first proposed and   *)
(* then chosen independently for each slot. No faults are modeled.         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Values, Slots

ASSUME ValuesAssumption == /\ Values # {}
                           /\ IsFiniteSet(Values)

ASSUME SlotsAssumption == IsFiniteSet(Slots)

(***************************************************************************
--algorithm MultiSlotConsensus
{
  variables proposed = {},
            chosen   = [s \in Slots |-> {}];

  define {
    Unproposed == Values \ proposed
    EmptySlots == {s \in Slots : chosen[s] = {}}
  }

  {
    while (TRUE) {
      either {
        with (v \in Values \ proposed) {
          proposed := proposed \cup {v}
        }
      }
      or {
        with (s \in {t \in Slots : chosen[t] = {}}, v \in proposed) {
          chosen[s] := {v}
        }
      }
    }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES proposed, chosen

(* define statement *)
Unproposed == Values \ proposed
EmptySlots == {s \in Slots : chosen[s] = {}}

vars == << proposed, chosen >>

Init == /\ proposed = {}
        /\ chosen = [s \in Slots |-> {}]

Propose == \E v \in Values \ proposed :
              /\ proposed' = proposed \cup {v}
              /\ UNCHANGED chosen

Choose == \E s \in {t \in Slots : chosen[t] = {}} :
            \E v \in proposed :
              /\ chosen' = [chosen EXCEPT ![s] = {v}]
              /\ UNCHANGED proposed

Next == Propose \/ Choose

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Next)
\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == /\ proposed \subseteq Values
          /\ chosen \in [Slots -> SUBSET Values]

Nontriviality == \A s \in Slots : chosen[s] \subseteq proposed

Consistency == \A s \in Slots : Cardinality(chosen[s]) <= 1

Inv == TypeOK /\ Nontriviality /\ Consistency

Stability == \A s \in Slots : \A v \in Values :
                [](v \in chosen[s] => [](v \in chosen[s]))

StableStep == [][\A s \in Slots : chosen[s] # {} => chosen'[s] = chosen[s]]_vars

(* Liveness property *)

AllSlotsChosen == \A s \in Slots : chosen[s] # {}

Liveness == <>AllSlotsChosen

THEOREM TypeCorrect    == Spec => []TypeOK
THEOREM NontrivialThm  == Spec => []Nontriviality
THEOREM ConsistentThm  == Spec => []Consistency
THEOREM StableThm      == Spec => Stability
THEOREM StableStepThm  == Spec => StableStep
THEOREM LivenessThm    == Spec => Liveness
=============================================================================