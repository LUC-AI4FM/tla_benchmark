----------------------------- MODULE CigaretteSmokers -----------------------------
EXTENDS Naturals, TLC

(*
  Parameters:
    - Ingredients: a finite set of ingredient names (e.g., {matches, paper, tobacco})
    - Offers: a set of subsets of Ingredients; each o \in Offers has size Cardinality(Ingredients) - 1
*)

CONSTANTS Ingredients, Offers

VARIABLES
  Table,     \* the set of ingredients currently on the table, or {} when the table is empty
  Smoking    \* the set of smokers currently smoking (identified by their owned ingredient)

Missing(S) == Ingredients \ S

Init ==
  /\ Smoking = {}
  /\ Table = {}

DealAct(o) ==
  /\ Smoking = {}
  /\ Table = {}
  /\ o \in Offers
  /\ Table' = o
  /\ UNCHANGED Smoking

StartAct(i) ==
  /\ Smoking = {}
  /\ Table \in Offers
  /\ i \in Ingredients
  /\ i \notin Table
  /\ Smoking' = {i}
  /\ Table' = {}

FinishAct(i) ==
  /\ Smoking = {i}
  /\ Smoking' = {}
  /\ UNCHANGED Table

Deal   == \E o \in Offers: DealAct(o)
Start  == \E i \in Ingredients: StartAct(i)
Finish == \E i \in Ingredients: FinishAct(i)

Next == Deal \/ Start \/ Finish

TypeOK ==
  /\ IsFiniteSet(Ingredients)
  /\ Cardinality(Ingredients) >= 2
  /\ Offers \subseteq SUBSET Ingredients
  /\ \A o \in Offers: Cardinality(o) = Cardinality(Ingredients) - 1
  /\ Smoking \subseteq Ingredients
  /\ (Table = {} \/ Table \in Offers)

AtMostOne == Cardinality(Smoking) <= 1

Fairness ==
  /\ WF_<<Table,Smoking>>(Deal)
  /\ \A i \in Ingredients: WF_<<Table,Smoking>>(StartAct(i))
  /\ \A i \in Ingredients: WF_<<Table,Smoking>>(FinishAct(i))

Spec == Init /\ [][Next]_<<Table,Smoking>> /\ Fairness

=============================================================================