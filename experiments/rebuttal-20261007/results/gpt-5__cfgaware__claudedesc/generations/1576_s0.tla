------------------------------ MODULE Deque ------------------------------

EXTENDS Sequences

CONSTANTS Val, Procs

null == "null"

VARIABLES queue, rV, pc

HeadElem(s) == s[1]
TailSeq(s)  == SubSeq(s, 2, Len(s))
LastElem(s) == s[Len(s)]
InitSeg(s)  == SubSeq(s, 1, Len(s) - 1)

Init ==
  /\ queue = << >>
  /\ rV = [p \in Procs |-> null]
  /\ pc = [p \in Procs |-> "L1"]

AEnqPrepend(p) ==
  \E v \in Val:
    /\ pc[p] = "L1"
    /\ queue' = << v >> \o queue
    /\ rV' = [rV EXCEPT ![p] = "ok"]
    /\ pc' = [pc EXCEPT ![p] = "L2"]

AEnqAppend(p) ==
  \E v \in Val:
    /\ pc[p] = "L1"
    /\ queue' = queue \o << v >>
    /\ rV' = [rV EXCEPT ![p] = "ok"]
    /\ pc' = [pc EXCEPT ![p] = "L2"]

AEnqDecline(p) ==
  /\ pc[p] = "L1"
  /\ queue' = queue
  /\ rV' = [rV EXCEPT ![p] = "full"]
  /\ pc' = [pc EXCEPT ![p] = "L2"]

ADeqHead(p) ==
  /\ pc[p] = "L1"
  /\ Len(queue) > 0
  /\ rV' = [rV EXCEPT ![p] = HeadElem(queue)]
  /\ queue' = TailSeq(queue)
  /\ pc' = [pc EXCEPT ![p] = "L2"]

ADeqTail(p) ==
  /\ pc[p] = "L1"
  /\ Len(queue) > 0
  /\ rV' = [rV EXCEPT ![p] = LastElem(queue)]
  /\ queue' = InitSeg(queue)
  /\ pc' = [pc EXCEPT ![p] = "L2"]

ADeqEmpty(p) ==
  /\ pc[p] = "L1"
  /\ Len(queue) = 0
  /\ queue' = queue
  /\ rV' = [rV EXCEPT ![p] = "empty"]
  /\ pc' = [pc EXCEPT ![p] = "L2"]

L1Act(p) ==
  AEnqPrepend(p) \/
  AEnqAppend(p)  \/
  AEnqDecline(p) \/
  ADeqHead(p)    \/
  ADeqTail(p)    \/
  ADeqEmpty(p)

L2Reset(p) ==
  /\ pc[p] = "L2"
  /\ queue' = queue
  /\ rV' = [rV EXCEPT ![p] = null]
  /\ pc' = [pc EXCEPT ![p] = "L1"]

ProcAct(p) == L1Act(p) \/ L2Reset(p)

Next == \E p \in Procs: ProcAct(p)

vars == << queue, rV, pc >>

Spec ==
  Init /\ [][Next]_vars /\ \A p \in Procs: WF_vars(ProcAct(p))

============================================================================