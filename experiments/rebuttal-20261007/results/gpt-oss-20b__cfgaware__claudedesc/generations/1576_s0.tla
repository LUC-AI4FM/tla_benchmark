------------------------------ MODULE DequeSpec ------------------------------
EXTENDS Naturals, Sequences, Temporal

(*--------------------------------------------------------------------------*)
(*  Constants supplied by the configuration                               *)
CONSTANTS Val, Procs, null
(*--------------------------------------------------------------------------*)

VARIABLES queue, rV

vars == {queue, rV}

(*--------------------------------------------------------------------------*)
(*  Initial state                                                            *)
Init ==
  /\ queue = <<>>
  /\ rV   = [p \in Procs |-> null]

(*--------------------------------------------------------------------------*)
(*  Enqueue operations                                                      *)
EnqueueBack(p, v) ==
  /\ queue' = Append(queue, v)
  /\ rV'    = [rV EXCEPT ![p] = v]

EnqueueFront(p, v) ==
  /\ queue' = Prepend(v, queue)
  /\ rV'    = [rV EXCEPT ![p] = v]

FullDecline(p) ==
  /\ queue' = queue
  /\ rV'    = [rV EXCEPT ![p] = "full"]

(*--------------------------------------------------------------------------*)
(*  Dequeue operations                                                      *)
DequeueNonEmptyHead(p) ==
  /\ queue # <<>>
  /\ queue' = Rest(queue)
  /\ rV'    = [rV EXCEPT ![p] = First(queue)]

DequeueNonEmptyTail(p) ==
  /\ queue # <<>>
  /\ queue' = SubSeq(queue, 1, Len(queue)-1)
  /\ rV'    = [rV EXCEPT ![p] = Last(queue)]

DequeueEmpty(p) ==
  /\ queue = <<>>
  /\ rV'   = [rV EXCEPT ![p] = "empty"]

(*--------------------------------------------------------------------------*)
(*  Operation step (L1)                                                     *)
DoOp(p) ==
  /\ rV[p] = null
  /\ ( (\E v \in Val : EnqueueBack(p, v))
       \/ (\E v \in Val : EnqueueFront(p, v))
       \/ FullDecline(p)
       \/ DequeueNonEmptyHead(p)
       \/ DequeueNonEmptyTail(p)
       \/ DequeueEmpty(p))

(*--------------------------------------------------------------------------*)
(*  Reset step (L2)                                                        *)
Reset(p) ==
  /\ rV[p] # null
  /\ rV'    = [rV EXCEPT ![p] = null]
  /\ queue'  = queue

(*--------------------------------------------------------------------------*)
(*  Next-state relation                                                    *)
Next ==
  \E p \in Procs : (DoOp(p) \/ Reset(p))

Proc(p) == DoOp(p) \/ Reset(p)

Spec == Init /\ [][Next]_vars /\ \A p \in Procs : WF_Proc(p)

EXPORTS Spec, Val
===============================================================================