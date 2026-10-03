------------------------------ MODULE ConcurrentQueue ------------------------------

EXTENDS Naturals, Sequences

CONSTANTS Procs, Val, N, Null

ASSUME N \in Nat
ASSUME Null \notin (Val \cup {"okay", "full", "empty"})

VARIABLES q, rV

vars == << q, rV >>

Status == {"okay", "full", "empty"}

Init ==
  /\ q = << >>
  /\ rV = [p \in Procs |-> Null]

EnqFront(p) ==
  \E v \in Val:
    \/ /\ Len(q) < N
       /\ q' = <<v>> \o q
       /\ rV' = [rV EXCEPT ![p] = "okay"]
    \/ /\ Len(q) >= N
       /\ q' = q
       /\ rV' = [rV EXCEPT ![p] = "full"]

EnqBack(p) ==
  \E v \in Val:
    \/ /\ Len(q) < N
       /\ q' = q \o <<v>>
       /\ rV' = [rV EXCEPT ![p] = "okay"]
    \/ /\ Len(q) >= N
       /\ q' = q
       /\ rV' = [rV EXCEPT ![p] = "full"]

DeqHead(p) ==
    \/ /\ Len(q) > 0
       /\ LET head == q[1] IN
            /\ q' = Tail(q)
            /\ rV' = [rV EXCEPT ![p] = head]
    \/ /\ Len(q) = 0
       /\ q' = q
       /\ rV' = [rV EXCEPT ![p] = "empty"]

DeqTail(p) ==
    \/ /\ Len(q) > 0
       /\ LET last == q[Len(q)] IN
            /\ q' = SubSeq(q, 1, Len(q) - 1)
            /\ rV' = [rV EXCEPT ![p] = last]
    \/ /\ Len(q) = 0
       /\ q' = q
       /\ rV' = [rV EXCEPT ![p] = "empty"]

P(p) == EnqFront(p) \/ EnqBack(p) \/ DeqHead(p) \/ DeqTail(p)

Next == \E p \in Procs: P(p)

TypeOK ==
  /\ q \in Seq(Val)
  /\ Len(q) <= N
  /\ rV \in [Procs -> (Val \cup Status \cup {Null})]

Bound == Len(q) <= N

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Procs: WF_vars(P(p))

=============================================================================