---------------------------- MODULE SharedDeque ----------------------------
EXTENDS Sequences, Integers

CONSTANTS Val, Procs, null

VARIABLES queue, rV, pc

vars == <<queue, rV, pc>>

TypeOK ==
    /\ queue \in Seq(Val)
    /\ rV \in [Procs -> Val \cup {null, "empty", "full"}]
    /\ pc \in [Procs -> {"L1", "L2"}]

Init ==
    /\ queue = <<>>
    /\ rV = [p \in Procs |-> null]
    /\ pc = [p \in Procs |-> "L1"]

Enqueue(p, v) ==
    /\ pc[p] = "L1"
    /\ \/ /\ queue' = Append(queue, v)
          /\ rV' = [rV EXCEPT ![p] = v]
       \/ /\ queue' = <<v>> \o queue
          /\ rV' = [rV EXCEPT ![p] = v]
       \/ /\ queue' = queue
          /\ rV' = [rV EXCEPT ![p] = "full"]
    /\ pc' = [pc EXCEPT ![p] = "L2"]

Dequeue(p) ==
    /\ pc[p] = "L1"
    /\ \/ /\ queue # <<>>
          /\ \/ /\ rV' = [rV EXCEPT ![p] = Head(queue)]
                /\ queue' = Tail(queue)
             \/ /\ rV' = [rV EXCEPT ![p] = queue[Len(queue)]]
                /\ queue' = SubSeq(queue, 1, Len(queue) - 1)
       \/ /\ queue = <<>>
          /\ rV' = [rV EXCEPT ![p] = "empty"]
          /\ queue' = queue
    /\ pc' = [pc EXCEPT ![p] = "L2"]

L1(p) ==
    \/ \E v \in Val : Enqueue(p, v)
    \/ Dequeue(p)

L2(p) ==
    /\ pc[p] = "L2"
    /\ rV' = [rV EXCEPT ![p] = null]
    /\ pc' = [pc EXCEPT ![p] = "L1"]
    /\ queue' = queue

Next ==
    \E p \in Procs : L1(p) \/ L2(p)

Fairness == \A p \in Procs : WF_vars(L1(p) \/ L2(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

QueueElementsValid == \A i \in 1..Len(queue) : queue[i] \in Val

ReturnValuesValid == \A p \in Procs : rV[p] \in Val \cup {null, "empty", "full"}

Safety == TypeOK /\ QueueElementsValid /\ ReturnValuesValid

Progress == \A p \in Procs : pc[p] = "L1" ~> pc[p] = "L2"

=============================================================================