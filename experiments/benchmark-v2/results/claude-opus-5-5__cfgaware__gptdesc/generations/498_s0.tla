---------------------------- MODULE MultiConsensus ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Values, Slots

(***************************************************************************
--algorithm MultiConsensus
variables proposed = {}, chosen = [s \in Slots |-> {}];
define
  TypeOK == /\ proposed \subseteq Values
            /\ chosen \in [Slots -> SUBSET Values]
  Nontriviality == \A s \in Slots : chosen[s] \subseteq proposed
  Consistency == \A s \in Slots : Cardinality(chosen[s]) <= 1
end define;
begin
  Loop:
    while TRUE do
      either
        with v \in Values \ proposed do
          proposed := proposed \union {v};
        end with;
      or
        with s \in {t \in Slots : chosen[t] = {}}, v \in proposed do
          chosen[s] := {v};
        end with;
      end either;
    end while;
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES proposed, chosen

TypeOK == /\ proposed \subseteq Values
          /\ chosen \in [Slots -> SUBSET Values]

Nontriviality == \A s \in Slots : chosen[s] \subseteq proposed

Consistency == \A s \in Slots : Cardinality(chosen[s]) <= 1

vars == << proposed, chosen >>

Init == /\ proposed = {}
        /\ chosen = [s \in Slots |-> {}]

Propose == \E v \in Values \ proposed :
              /\ proposed' = proposed \union {v}
              /\ UNCHANGED chosen

Choose == \E s \in {t \in Slots : chosen[t] = {}} :
            \E v \in proposed :
              /\ chosen' = [chosen EXCEPT ![s] = {v}]
              /\ UNCHANGED proposed

Terminating == /\ \A s \in Slots : chosen[s] # {}
               /\ proposed = Values
               /\ UNCHANGED vars

Next == Propose \/ Choose \/ Terminating

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

LiveSpec == Spec /\ WF_vars(Next)

Stability ==
  \A s \in Slots : \A v \in Values :
     [](v \in chosen[s] => [](v \in chosen[s]))

Liveness == \A s \in Slots : <>(chosen[s] # {})

THEOREM Spec => [](TypeOK /\ Nontriviality /\ Consistency)
THEOREM Spec => Stability
THEOREM LiveSpec => Liveness
===============================================================================