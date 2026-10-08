---------------------------- MODULE MultiInstanceConsensus ----------------------------
EXTENDS Integers, TLC

CONSTANT Values, Slots
VARIABLE proposed, chosen

TypeInvariant == /\ proposed \in [Slots -> SUBSET Values]
                  /\ chosen \in [Slots -> Values \cup {<<>>}]
Nontriviality == []<>~(chosen' = <<>>) /\ proposed' /= {}
Stability == []<>(chosen' = chosen)
Consistency == []<>(chosen' \cap chosen) = chosen'
Liveness == <>[]<>(chosen' = chosen)

Propose(v, s) == /\ ~<<>> \in chosen
                 /\ v \in Values
                 /\ proposed' = [proposed EXCEPT ![s] = {v} \cup @]
Choose(s) == /\ <<>> \in chosen
              /\ proposed' = proposed
              /\ chosen' = [chosen EXCEPT ![s] = CHOOSE v \in proposed[s]: TRUE]

Next == (\E s \in Slots, v \in Values : Propose(v, s)) \/ (\E s \in Slots : Choose(s))
Spec == /\ TypeInvariant
         /\ proposed = [s \in Slots |-> {}]
         /\ chosen = [s \in Slots |-> <<>>]
         /\ [][Next]_proposed \* [][Next]_chosen

LiveSpec == Spec /\ WF_vars(Next, proposed, chosen)
=============================================================================