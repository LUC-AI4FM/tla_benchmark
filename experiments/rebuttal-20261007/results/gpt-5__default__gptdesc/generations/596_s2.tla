----------------------------- MODULE OneVarSystem -----------------------------

EXTENDS Integers, Sequences

CONSTANT CEX

VARIABLES x

Init ==
  x = 0

Next ==
  \/ /\ x = 0
     /\ x' \in {1, 2}
  \/ /\ x # 0
     /\ x' = 0

Spec ==
  Init /\ [] [Next]_x /\ WF_x(Next)

\* Safety invariant
TypeInv ==
  x \in {0, 1, 2}

\* Temporal properties
StabilizeAwayFrom1 ==
  <>[] (x # 1)

StabilizeAwayFrom2 ==
  <>[] (x # 2)

StabilizeAwayFromEither ==
  (<>[] (x # 1)) \/ (<>[] (x # 2))

NegStabilizeAwayFrom1 ==
  ~StabilizeAwayFrom1

RecurZero ==
  []<> (x = 0)

\* Postcondition for TLC: checks a counterexample trace encoded
\* as a sequence (tuple) of records, with tuple and set fields.
Post ==
  /\ CEX \in Seq([ x : {0,1,2}, info : <<0,1,2>>, choices : {1,2} ])
  /\ Len(CEX) >= 3
  /\ CEX[1].x = 0
  /\ CEX[2].x \in {1,2}
  /\ CEX[3].x = 0
  /\ \A i \in 1..Len(CEX):
       /\ CEX[i].info = <<0,1,2>>
       /\ CEX[i].choices = {1,2}

============================================================================