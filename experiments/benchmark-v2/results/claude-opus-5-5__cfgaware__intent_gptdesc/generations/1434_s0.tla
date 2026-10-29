---- MODULE PossibleStates ----
EXTENDS Naturals, FiniteSets, TLC

VARIABLE x

vars == <<x>>

Values == {0, 1, 2, 3, 4, 5}

InitVal == 0

Init == x = InitVal

\* Alternatives A1..A4 all allow the same next-state value 5.
\* They differ only syntactically, so a model checker may generate
\* duplicate successor states for them.

\* A1: the assignment comes before the disjunction.
A1 == x' = 5 /\ (x = 0 \/ x = 1)

\* A2: the assignment comes after the disjunction.
A2 == (x = 0 \/ x = 1) /\ x' = 5

\* A3: the assignment is pushed inside each disjunct.
\* An eager evaluator generates two identical successors.
A3 == (x = 0 /\ x' = 5) \/ (x = 0 /\ x' = 5)

\* A4: the membership conjunct is wrapped in an IF so it is not
\* evaluated eagerly as a generator.
A4 == x' \in {5} /\ IF x \in {0, 1} THEN TRUE ELSE FALSE

\* Semantically distinct alternatives.
A5 == x' = 3 /\ x \in {0, 5}
A6 == x' = 1 /\ x = 0
A7 == x' = 0   \* always enabled, so there is no deadlock

Next == A1 \/ A2 \/ A3 \/ A4 \/ A5 \/ A6 \/ A7

Spec == Init /\ [][Next]_vars

\* Semantic successor set of a state value v. This removes the
\* syntactic duplicates produced by A1..A4.
Succ(v) == { w \in Values :
               \/ (w = 5 /\ v \in {0, 1})
               \/ (w = 3 /\ v \in {0, 5})
               \/ (w = 1 /\ v = 0)
               \/ w = 0 }

\* Number of syntactic alternatives enabled from v that lead to the
\* target 5. Duplicates are counted with multiplicity.
SyntacticFiveCount(v) ==
    (IF v \in {0, 1} THEN 1 ELSE 0)   \* A1
  + (IF v \in {0, 1} THEN 1 ELSE 0)   \* A2
  + (IF v = 0 THEN 2 ELSE 0)          \* A3 (two identical disjuncts)
  + (IF v \in {0, 1} THEN 1 ELSE 0)   \* A4

\* Safety invariant: x always stays within the allowed values.
Inv == x \in Values

\* Predicate that is true only in the state where x = 5.
HasFive == x = 5

\* The initial state can be left: some transition changes the value.
LeaveInit ==
    x = InitVal => \E w \in Succ(x) : w # InitVal

\* Expectations about distinct versus duplicate successor states.
\* From the initial value there are 4 distinct semantic successors
\* {0, 1, 3, 5}. Five syntactic alternatives yield the value 5,
\* but they collapse into one distinct state.
PossibleCounts ==
    /\ Cardinality(Succ(InitVal)) = 4
    /\ Succ(InitVal) = {0, 1, 3, 5}
    /\ SyntacticFiveCount(InitVal) = 5
    /\ Cardinality({w \in Succ(InitVal) : w = 5}) = 1
    /\ Cardinality(Succ(5)) = 2

\* Named "possible" properties: the states the model checker should
\* report as reachable or satisfiable.
_POSSIBLE ==
    /\ \E w \in Succ(InitVal) : w = 5     \* HasFive is possible
    /\ \E w \in Succ(InitVal) : w # InitVal \* LeaveInit is possible
    /\ x \in Values

====