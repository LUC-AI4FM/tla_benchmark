------------------------------- MODULE MultiSlotConsensus -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Values, Slots

ASSUME ValuesAssump == Values # {} /\ IsFiniteSet(Values)
ASSUME SlotsAssump  == IsFiniteSet(Slots)

(***************************************************************************
--algorithm MultiSlotConsensus
variables proposed = {},
          chosen = [s \in Slots |-> {}];
begin
Lbl: while TRUE do
       either
         with v \in Values \ proposed do
           proposed := proposed \cup {v}
         end with
       or
         with s \in {t \in Slots : chosen[t] = {}}, v \in proposed do
           chosen[s] := {v}
         end with
       end either
     end while
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES proposed, chosen, pc

vars == << proposed, chosen, pc >>

Init == /\ proposed = {}
        /\ chosen = [s \in Slots |-> {}]
        /\ pc = "Lbl"

Propose == /\ pc = "Lbl"
           /\ \E v \in Values \ proposed :
                 proposed' = proposed \cup {v}
           /\ pc' = "Lbl"
           /\ UNCHANGED chosen

Choose == /\ pc = "Lbl"
          /\ \E s \in {t \in Slots : chosen[t] = {}} :
               \E v \in proposed :
                  chosen' = [chosen EXCEPT ![s] = {v}]
          /\ pc' = "Lbl"
          /\ UNCHANGED proposed

Lbl == Propose \/ Choose

Next == Lbl

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
\* END TRANSLATION

-----------------------------------------------------------------------------------------
\* Safety properties

TypeOK == /\ proposed \subseteq Values
          /\ chosen \in [Slots -> SUBSET Values]
          /\ pc = "Lbl"

\* Only proposed values may be chosen
Nontriviality == \A s \in Slots : chosen[s] \subseteq proposed

\* At most one value is chosen per slot
Consistency == \A s \in Slots : Cardinality(chosen[s]) <= 1

Inv == TypeOK /\ Nontriviality /\ Consistency

\* Once a value is chosen for a slot, it never changes
Stability == [][\A s \in Slots : chosen[s] # {} => chosen'[s] = chosen[s]]_vars

-----------------------------------------------------------------------------------------
\* Liveness property

AllSlotsChosen == \A s \in Slots : chosen[s] # {}

Liveness == <>AllSlotsChosen

-----------------------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Nontriviality
THEOREM Spec => []Consistency
THEOREM Spec => Stability
THEOREM Spec => Liveness
=========================================================================================