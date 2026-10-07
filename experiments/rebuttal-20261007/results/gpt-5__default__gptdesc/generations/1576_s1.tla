----------------------------- MODULE ConcurrentQueue -----------------------------

EXTENDS Naturals, Sequences

CONSTANTS Procs, Val, N, OK, FULL, EMPTY, Null

ASSUME
  /\ N \in Nat
  /\ {OK, FULL, EMPTY, Null} \cap Val = {}
  /\ OK /= FULL /\ OK /= EMPTY /\ OK /= Null
  /\ FULL /= EMPTY /\ FULL /= Null
  /\ EMPTY /= Null

VARIABLES queue, rV

vars == << queue, rV >>

RVal == Val \cup {OK, FULL, EMPTY, Null}

Init ==
  /\ queue = << >>
  /\ rV = [p \in Procs |-> Null]

EnqFront(self, v) ==
  /\ v \in Val
  /\ IF Len(queue) < N
        THEN /\ queue' = << v >> \o queue
             /\ rV' = [rV EXCEPT ![self] = OK]
        ELSE /\ UNCHANGED queue
             /\ rV' = [rV EXCEPT ![self] = FULL]

EnqBack(self, v) ==
  /\ v \in Val
  /\ IF Len(queue) < N
        THEN /\ queue' = Append(queue, v)
             /\ rV' = [rV EXCEPT ![self] = OK]
        ELSE /\ UNCHANGED queue
             /\ rV' = [rV EXCEPT ![self] = FULL]

DeqFront(self) ==
  IF Len(queue) > 0
    THEN LET val == Head(queue) IN
         /\ queue' = Tail(queue)
         /\ rV' = [rV EXCEPT ![self] = val]
    ELSE /\ UNCHANGED queue
         /\ rV' = [rV EXCEPT ![self] = EMPTY]

DeqBack(self) ==
  IF Len(queue) > 0
    THEN LET n == Len(queue)
             val == queue[n]
             rest == IF n = 1 THEN << >> ELSE SubSeq(queue, 1, n-1)
         IN  /\ queue' = rest
             /\ rV' = [rV EXCEPT ![self] = val]
    ELSE /\ UNCHANGED queue
         /\ rV' = [rV EXCEPT ![self] = EMPTY]

P(self) ==
  \/ \E v \in Val: EnqFront(self, v)
  \/ \E v \in Val: EnqBack(self, v)
  \/ DeqFront(self)
  \/ DeqBack(self)

Next ==
  \E self \in Procs: P(self)

Constraint ==
  Len(queue) <= N

TypeInv ==
  /\ queue \in Seq(Val)
  /\ rV \in [Procs -> RVal]
  /\ Len(queue) <= N

Safety ==
  []TypeInv

Liveness ==
  \A self \in Procs: WF_vars(P(self))

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Liveness
  /\ []Constraint

=============================================================================