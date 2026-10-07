------------------------------ MODULE ConcurrentQueue ------------------------------

EXTENDS Naturals, Sequences

CONSTANTS
  Procs, \* nonempty set of process identifiers
  Val,   \* set of values that can be enqueued/dequeued
  N,     \* queue capacity bound (a natural number)
  OK, FULL, EMPTY, Null \* distinct return/status values

ASSUME N \in Nat

VARIABLES q, rV

vars == << q, rV >>

Head(s) == s[1]
Last(s) == s[Len(s)]
Tail(s) == IF Len(s) = 1 THEN << >> ELSE SubSeq(s, 2, Len(s))
Front(s) == IF Len(s) = 1 THEN << >> ELSE SubSeq(s, 1, Len(s) - 1)

RetVals == Val \cup {OK, FULL, EMPTY, Null}

TypeInv ==
  /\ q \in Seq(Val)
  /\ rV \in [Procs \rightarrow RetVals]

BoundInv == Len(q) <= N

Init ==
  /\ q = << >>
  /\ rV = [p \in Procs |-> Null]

EnqFrontOK(p) ==
  \E v \in Val:
    /\ Len(q) < N
    /\ q' = << v >> \o q
    /\ rV' = [rV EXCEPT ![p] = OK]

EnqBackOK(p) ==
  \E v \in Val:
    /\ Len(q) < N
    /\ q' = Append(q, v)
    /\ rV' = [rV EXCEPT ![p] = OK]

EnqFrontFull(p) ==
  /\ Len(q) = N
  /\ q' = q
  /\ rV' = [rV EXCEPT ![p] = FULL]

EnqBackFull(p) ==
  /\ Len(q) = N
  /\ q' = q
  /\ rV' = [rV EXCEPT ![p] = FULL]

DeqHeadOK(p) ==
  /\ Len(q) > 0
  /\ q' = Tail(q)
  /\ rV' = [rV EXCEPT ![p] = Head(q)]

DeqTailOK(p) ==
  /\ Len(q) > 0
  /\ q' = Front(q)
  /\ rV' = [rV EXCEPT ![p] = Last(q)]

DeqHeadEmpty(p) ==
  /\ Len(q) = 0
  /\ q' = q
  /\ rV' = [rV EXCEPT ![p] = EMPTY]

DeqTailEmpty(p) ==
  /\ Len(q) = 0
  /\ q' = q
  /\ rV' = [rV EXCEPT ![p] = EMPTY]

P(p) ==
  \* Process p may perform any of the following atomic actions:
  \/ EnqFrontOK(p)
  \/ EnqBackOK(p)
  \/ EnqFrontFull(p)
  \/ EnqBackFull(p)
  \/ DeqHeadOK(p)
  \/ DeqTailOK(p)
  \/ DeqHeadEmpty(p)
  \/ DeqTailEmpty(p)

Next ==
  \E p \in Procs: P(p)

StateConstraint == [](Len(q) <= N)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Procs: WF_vars(P(p))
  /\ StateConstraint

Safety == [](TypeInv /\ BoundInv)

=============================================================================