----------------------------- MODULE Deque -----------------------------

EXTENDS Naturals, Sequences

CONSTANTS Val, Procs, null

VARIABLES queue, rV, pc

vars == << queue, rV, pc >>

Last(s) == s[Len(s)]
ButLast(s) == SubSeq(s, 1, Len(s) - 1)

Init ==
  /\ queue = << >>
  /\ rV = [p \in Procs |-> null]
  /\ pc = [p \in Procs |-> "L1"]

L1Enq(p) ==
  /\ pc[p] = "L1"
  /\ \E v \in Val:
       \/ /\ queue' = Append(queue, v)
          /\ rV' = [rV EXCEPT ![p] = "ok"]
          /\ pc' = [pc EXCEPT ![p] = "L2"]
       \/ /\ queue' = << v >> \o queue
          /\ rV' = [rV EXCEPT ![p] = "ok"]
          /\ pc' = [pc EXCEPT ![p] = "L2"]
       \/ /\ queue' = queue
          /\ rV' = [rV EXCEPT ![p] = "full"]
          /\ pc' = [pc EXCEPT ![p] = "L2"]

L1Deq(p) ==
  /\ pc[p] = "L1"
  /\ ( \/ /\ queue # << >>
         /\ ( \/ /\ queue' = Tail(queue)
               /\ rV' = [rV EXCEPT ![p] = Head(queue)]
               /\ pc' = [pc EXCEPT ![p] = "L2"]
              \/ /\ queue' = ButLast(queue)
               /\ rV' = [rV EXCEPT ![p] = Last(queue)]
               /\ pc' = [pc EXCEPT ![p] = "L2"] )
     \/ /\ queue = << >>
         /\ queue' = queue
         /\ rV' = [rV EXCEPT ![p] = "empty"]
         /\ pc' = [pc EXCEPT ![p] = "L2"] )

L1Step(p) == L1Enq(p) \/ L1Deq(p)

L2Step(p) ==
  /\ pc[p] = "L2"
  /\ queue' = queue
  /\ rV' = [rV EXCEPT ![p] = null]
  /\ pc' = [pc EXCEPT ![p] = "L1"]

Next ==
  \E p \in Procs:
    L1Step(p) \/ L2Step(p)

TypeOK ==
  /\ queue \in Seq(Val)
  /\ rV \in [Procs -> (Val \cup { "empty", "full", "ok", null })]
  /\ pc \in [Procs -> { "L1", "L2" }]

RValDiscipline ==
  \A p \in Procs:
    /\ (pc[p] = "L1" => rV[p] = null)
    /\ (pc[p] = "L2" => rV[p] # null)

Fairness ==
  \A p \in Procs:
    /\ WF_vars(L1Step(p))
    /\ WF_vars(L2Step(p))

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

=======================================================================