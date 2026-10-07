----------------------------- MODULE OneVarWF -----------------------------

EXTENDS Naturals, Sequences

CONSTANTS Dummy

VARIABLES x

Values == {0, 1, 2}

Init == x = 0

Next ==
  \/ /\ x = 0
     /\ x' \in {1, 2}
  \/ /\ x \in {1, 2}
     /\ x' = 0

TypeInv == x \in Values

Spec == Init /\ [][Next]_x /\ WF_x(Next)

\* Safety invariant
Inv == TypeInv

\* Liveness: eventual repeated return to zero (infinitely often at 0)
RecurZero == []<>(x = 0)

\* Liveness: eventual stabilization away from 1
StabilizeNot1 == <>[](x # 1)

\* Liveness: eventual stabilization away from 2
StabilizeNot2 == <>[](x # 2)

\* Disjunction: eventually stabilizes away from 1 or from 2
OneStabilizes == StabilizeNot1 \/ StabilizeNot2

\* The negation of one temporal property
NegStabilizeNot1 == ~StabilizeNot1

\* Postcondition: checks a TLC-generated counterexample trace encoded using records, tuples, and sets.
\* This is a state predicate that can be used as a Postcondition in a TLC model.
PostCondition ==
  LET rec == [ s1 |-> 0, s2 |-> 1, s3 |-> 0 ]
      tup == <<0, 1, 0, 2, 0>>
      set == {0, 1, 2}
  IN /\ rec.s1 = 0
     /\ rec.s2 = 1
     /\ rec.s3 \in set
     /\ tup \in Seq(set)
     /\ x \in set

\* Useful theorems (for documentation; proofs omitted)
THEOREM Spec => []Inv
THEOREM Spec => RecurZero

============================================================================