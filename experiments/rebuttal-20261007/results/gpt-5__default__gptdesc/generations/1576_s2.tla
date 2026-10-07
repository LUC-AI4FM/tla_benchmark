----------------------------- MODULE ConcurrentQueue -----------------------------

EXTENDS Naturals, Sequences

CONSTANTS Procs, Val, N

ASSUME
  /\ N \in Nat
  /\ Val # {}
  /\ Procs # {}

VARIABLES q, rV

vars == << q, rV >>

RValSet == Val \cup {"okay", "full", "empty", "null"}

Init ==
  /\ q = << >>
  /\ rV = [p \in Procs |-> "null"]

P(p) ==
  \E op \in {"enqFront", "enqBack", "deqFront", "deqBack"} :
    IF op \in {"enqFront", "enqBack"} THEN
      \E v \in Val :
        IF Len(q) < N THEN
          /\ q' = IF op = "enqFront" THEN <<v>> \o q ELSE Append(q, v)
          /\ rV' = [rV EXCEPT ![p] = "okay"]
        ELSE
          /\ q' = q
          /\ rV' = [rV EXCEPT ![p] = "full"]
    ELSE
      /\ Len(q) > 0
      /\ IF op = "deqFront" THEN
            /\ rV' = [rV EXCEPT ![p] = q[1]]
            /\ q' = SubSeq(q, 2, Len(q))
         ELSE
            /\ rV' = [rV EXCEPT ![p] = q[Len(q)]]
            /\ q' = SubSeq(q, 1, Len(q) - 1)

Next == \E p \in Procs : P(p)

TypeOK ==
  /\ q \in Seq(Val)
  /\ rV \in [Procs -> RValSet]

StateConstraint == Len(q) <= N

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Procs : WF_vars(P(p))
  /\ []StateConstraint

=============================================================================