------------------------------ MODULE DijkstraRing ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS N, K

VARIABLES vals

Pred(i) == IF i = 1 THEN N ELSE i - 1

Proc(i) ==
   IF i = 1 THEN
      IF vals[1] = vals[N] THEN
         vals' = [vals EXCEPT ![1] = (vals[1] + 1) % K]
      ELSE
         UNCHANGED vals
   ELSE
      IF vals[i] # vals[Pred(i)] THEN
         vals' = [vals EXCEPT ![i] = vals[Pred(i)]]
      ELSE
         UNCHANGED vals

Next == ∃ i \in 1..N : Proc(i)

Init == vals \in [1..N -> 0..K-1]

vars == {vals}

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

SomeoneHoldsToken ==
   ∃ i \in 1..N :
      vals[i] # vals[Pred(i)]

EventuallyJustOneHoldsToken ==
   <> (∃ i \in 1..N :
        vals[i] # vals[Pred(i)] /\
        ∀ j \in 1..N : (vals[j] # vals[Pred(j)]) => j = i)

=============================================================================