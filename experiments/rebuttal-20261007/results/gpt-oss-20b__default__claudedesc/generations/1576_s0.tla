MODULE DequeSpec
EXTENDS Naturals, Sequences

CONSTANTS Val, Procs, null, Full, Empty, N

VARIABLES queue, rV, phase

(* Helper function to remove the last element of a sequence *)
Front(q) == IF Len(q)=0 THEN <<>> ELSE SubSeq(q, 1, Len(q)-1)

Init ==
  /\ queue = <<>>
  /\ rV   = [p \in Procs |-> null]
  /\ phase= [p \in Procs |-> "L1"]

(* Body of an enqueue operation *)
EnqueueBody(p) ==
  /\ v \in Val
  /\ (
        /\ queue' = queue ^ <<v>>
        /\ rV'   = [rV EXCEPT ![p] = v]
     \/ /\ queue' = <<v>> ^ queue
        /\ rV'   = [rV EXCEPT ![p] = v]
     \/ /\ queue' = queue
        /\ rV'   = [rV EXCEPT ![p] = Full]
      )

(* Body of a dequeue operation *)
DequeueBody(p) ==
  /\ IF Len(queue) > 0 THEN
        \/ ( /* pop head */
            /\ removed = First(queue)
            /\ queue' = Tail(queue)
            /\ rV'   = [rV EXCEPT ![p] = removed]
          )
        \/ ( /* pop tail */
            /\ removed = Last(queue)
            /\ queue' = Front(queue)
            /\ rV'   = [rV EXCEPT ![p] = removed]
          )
     ELSE
        /\ queue' = queue
        /\ rV'   = [rV EXCEPT ![p] = Empty]

(* Action for a process in phase L1: perform an operation *)
DoOp(p) ==
  /\ phase[p] = "L1"
  /\ ( EnqueueBody(p) \/ DequeueBody(p) )
  /\ phase'[p] = "L2"

(* Action for a process in phase L2: reset return value *)
Reset(p) ==
  /\ phase[p] = "L2"
  /\ rV'   = [rV EXCEPT ![p] = null]
  /\ phase'[p] = "L1"
  /\ queue' = queue

Next == ∃ p \in Procs : (DoOp(p) \/ Reset(p))

vars == {queue, rV, phase}

(* Safety invariant: queue length bounded by N *)
Inv == Len(queue) <= N

Spec == Init /\ [][Next]_(vars) /\ WF_{p \in Procs} DoOp(p)

=============================================================================
END MODULE