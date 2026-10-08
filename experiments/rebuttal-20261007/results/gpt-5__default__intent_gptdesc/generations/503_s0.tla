---------------------------- MODULE ConsensusCore ----------------------------

EXTENDS Naturals

CONSTANTS Proc, VALUES, NoValue

ASSUME NoValue \notin VALUES

VARIABLES 
  chosen,       \* the currently chosen value, or NoValue if none chosen yet
  proposed,     \* set of values that have been proposed by any process
  propBy,       \* mapping from processes to the set of values they have proposed
  learned,      \* mapping from processes to what value they have learned (or NoValue)
  chosenSet     \* history set of all values that have ever been chosen (at most one)

vars == << chosen, proposed, propBy, learned, chosenSet >>

TypeOK ==
  /\ chosen \in VALUES \cup {NoValue}
  /\ proposed \subseteq VALUES
  /\ propBy \in [Proc -> SUBSET VALUES]
  /\ learned \in [Proc -> (VALUES \cup {NoValue})]
  /\ chosenSet \subseteq VALUES

\* Safety: validity (chosen always from allowed set or NoValue)
ValidityInv == (chosen = NoValue) \/ (chosen \in VALUES)

\* Safety: agreement (no two distinct values are ever chosen)
AgreementInv == \A v1 \in chosenSet: \A v2 \in chosenSet: v1 = v2

\* Optional strengthening: any chosen value was proposed (holds in this model)
ChosenFromProposalsInv == (chosen = NoValue) \/ (chosen \in proposed)

Init ==
  /\ chosen = NoValue
  /\ proposed = {}
  /\ propBy = [p \in Proc |-> {}]
  /\ learned = [p \in Proc |-> NoValue]
  /\ chosenSet = {}

Propose(p, v) ==
  /\ p \in Proc
  /\ v \in VALUES
  /\ propBy' = [propBy EXCEPT ![p] = @ \cup {v}]
  /\ proposed' = proposed \cup {v}
  /\ UNCHANGED << chosen, learned, chosenSet >>

Choose(v) ==
  /\ chosen = NoValue
  /\ v \in proposed
  /\ chosen' = v
  /\ chosenSet' = chosenSet \cup {v}
  /\ UNCHANGED << proposed, propBy, learned >>

Learn(p) ==
  /\ p \in Proc
  /\ chosen # NoValue
  /\ learned' = [learned EXCEPT ![p] = chosen]
  /\ UNCHANGED << chosen, proposed, propBy, chosenSet >>

ProposeAct == \E p \in Proc, v \in VALUES: Propose(p, v)
ChooseAct  == \E v \in proposed: Choose(v)
LearnAct   == \E p \in Proc: Learn(p)

Next ==
  \/ ProposeAct
  \/ ChooseAct
  \/ LearnAct

Spec == Init /\ [][Next]_vars

\* Fairness assumption (optional): if ChooseAct remains continuously enabled, it will eventually occur.
Fairness == SF_vars(ChooseAct)

\* Spec under the above fairness assumption.
FairSpec == Spec /\ Fairness

\* Liveness (under FairSpec): once some proposal exists, eventually a value is chosen.
EventualChoice == (<>(proposed # {})) => <>(chosen # NoValue)

\* Nontriviality: if no proposal ever occurs, then choosing nothing is permitted (chosen stays NoValue).
Nontriviality == ([](proposed = {})) => [](chosen = NoValue)

\* Integrity (temporal safety): once a value is chosen, it never changes thereafter.
Integrity == []( (chosen # NoValue) => [](chosen' = chosen) )

\* Aggregate safety predicate for convenience.
Safety == [](TypeOK /\ ValidityInv /\ AgreementInv /\ ChosenFromProposalsInv)

=============================================================================