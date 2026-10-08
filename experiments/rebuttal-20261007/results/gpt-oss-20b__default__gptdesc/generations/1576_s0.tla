MODULE QueueSpec
EXTENDS Sequences, TLC

CONSTANTS Procs, Val, N, Okay, Full, Empty, Null

VARIABLES queue, rV

TypeInv == queue \in Seq(Val) /\ Len(queue) <= N /\
          rV \in [Procs -> (Val ∪ {Okay, Full, Empty, Null})]

Init == queue = <<>> /\ rV = [p \in Procs |-> Null] /\ TypeInv

EnqFront(p) ==
  \E v \in Val :
    /\ Len(queue) < N
    /\ queue' = <<v>> ^ queue
    /\ rV' = [rV EXCEPT ![p] = Okay]

EnqBack(p) ==
  \E v \in Val :
    /\ Len(queue) < N
    /\ queue' = queue ^ <<v>>
    /\ rV' = [rV EXCEPT ![p] = Okay]

EnqFrontFull(p) ==
  /\ Len(queue) >= N
  /\ queue' = queue
  /\ rV' = [rV EXCEPT ![p] = Full]

EnqBackFull(p) ==
  /\ Len(queue) >= N
  /\ queue' = queue
  /\ rV' = [rV EXCEPT ![p] = Full]

DeqHeadNonEmpty(p) ==
  \E v \in Val :
    /\ Len(queue) > 0
    /\ v = Head(queue)
    /\ queue' = Tail(queue)
    /\ rV' = [rV EXCEPT ![p] = v]

DeqTailNonEmpty(p) ==
  \E v \in Val :
    /\ Len(queue) > 0
    /\ v = Last(queue)
    /\ queue' = Init(queue)
    /\ rV' = [rV EXCEPT ![p] = v]

DeqHeadEmpty(p) ==
  /\ Len(queue) = 0
  /\ queue' = queue
  /\ rV' = [rV EXCEPT ![p] = Empty]

DeqTailEmpty(p) ==
  /\ Len(queue) = 0
  /\ queue' = queue
  /\ rV' = [rV EXCEPT ![p] = Empty]

P(p) == EnqFront(p) \/ EnqBack(p) \/ EnqFrontFull(p) \/ EnqBackFull(p) \/
        DeqHeadNonEmpty(p) \/ DeqTailNonEmpty(p) \/ DeqHeadEmpty(p) \/ DeqTailEmpty(p)

Stutter == UNCHANGED <<queue, rV>>

Next == (\E p \in Procs : P(p)) \/ Stutter

Spec == Init /\ [][Next]_{queue, rV} /\ TypeInv /\ \A p \in Procs : WF_0(P(p))
===============================================================================