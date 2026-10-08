MODULE ConcurrentQueue
EXTENDS Naturals, Sequences

CONSTANTS Procs, Val, N

VARIABLES queue, rV

(* Helper definitions *)
Head(q) == q[1]
TailSeq(q) == IF Len(q) > 0 THEN SubSeq(q,2,Len(q)) ELSE <<>>
LastElem(q) == q[Len(q)]
InitSeq(q) == IF Len(q) > 0 THEN SubSeq(q,1,Len(q)-1) ELSE <<>>

(* Type invariant *)
TypeInv ==
  /\ queue \in Seq(Val)
  /\ rV \in [Procs -> {"okay","full","empty","null"} ∪ Val]
  /\ Len(queue) <= N

Init ==
  /\ queue = << >>
  /\ rV = [p \in Procs |-> "null"]
  /\ TypeInv

(* Actions *)

EnqFSucc(p, v) ==
  /\ p \in Procs
  /\ v \in Val
  /\ Len(queue) < N
  /\ queue' = <<v>> ^ queue
  /\ rV' = [rV EXCEPT ![p] = "okay"]

EnqFFull(p, v) ==
  /\ p \in Procs
  /\ v \in Val
  /\ Len(queue) >= N
  /\ queue' = queue
  /\ rV' = [rV EXCEPT ![p] = "full"]

EnqBSucc(p, v) ==
  /\ p \in Procs
  /\ v \in Val
  /\ Len(queue) < N
  /\ queue' = queue ^ <<v>>
  /\ rV' = [rV EXCEPT ![p] = "okay"]

EnqBFull(p, v) ==
  /\ p \in Procs
  /\ v \in Val
  /\ Len(queue) >= N
  /\ queue' = queue
  /\ rV' = [rV EXCEPT ![p] = "full"]

DeqHSucc(p) ==
  /\ p \in Procs
  /\ Len(queue) > 0
  /\ LET e == Head(queue) IN 
       /\ queue' = TailSeq(queue)
       /\ rV' = [rV EXCEPT ![p] = e]

DeqHEmpty(p) ==
  /\ p \in Procs
  /\ Len(queue) = 0
  /\ queue' = queue
  /\ rV' = [rV EXCEPT ![p] = "empty"]

DeqTSucc(p) ==
  /\ p \in Procs
  /\ Len(queue) > 0
  /\ LET e == LastElem(queue) IN 
       /\ queue' = InitSeq(queue)
       /\ rV' = [rV EXCEPT ![p] = e]

DeqTEmpty(p) ==
  /\ p \in Procs
  /\ Len(queue) = 0
  /\ queue' = queue
  /\ rV' = [rV EXCEPT ![p] = "empty"]

Stutter == UNCHANGED <<queue, rV>>

Next