---------------------------- MODULE QueueSystem ----------------------------
EXTENDS Integers, Sequences

CONSTANT Procs, Val, N

VARIABLE queue, rV

Init == (* Initial condition *)
        /\ queue = <<>>
        /\ rV = [i \in Procs |-> NULL]

Next == (* Next-state relation *)
  \/ \E p \in Procs :
    (* Enqueue at front *)
    (rV' = [rV EXCEPT ![p] = "okay"])
    /\ (queue' = Prepend(queue, Val))
    /\ (Len(queue') <= N)
  \/ \E p \in Procs :
    (* Enqueue at back *)
    (rV' = [rV EXCEPT ![p] = "okay"])
    /\ (queue' = Append(queue, Val))
    /\ (Len(queue') <= N)
  \/ \E p \in Procs :
    (* Dequeue from head *)
    (queue # <<>>)
    /\ (rV' = [rV EXCEPT ![p] = Head(queue)])
    /\ (queue' = Tail(queue))
  \/ \E p \in Procs :
    (* Dequeue from tail *)
    (queue # <<>>)
    /\ (rV' = [rV EXCEPT ![p] = Last(queue)])
    /\ (queue' = SubSeq(queue, 1, Len(queue) - 1))
  \/ (* Stuttering step *)
      (queue' = queue)
      /\ (rV' = rV)

Spec == (* Temporal specification *)
        Init /\ [][Next]_<<queue, rV>>
        /\ \A p \in Procs : WF_vars(Next_p(p), <<queue, rV>>)

Next_p(p) == (* Next-state relation for process p *)
  \/ (* Enqueue at front *)
    (rV' = [rV EXCEPT ![p] = "okay"])
    /\ (queue' = Prepend(queue, Val))
    /\ (Len(queue') <= N)
  \/ (* Enqueue at back *)
    (rV' = [rV EXCEPT ![p] = "okay"])
    /\ (queue' = Append(queue, Val))
    /\ (Len(queue') <= N)
  \/ (* Dequeue from head *)
    (queue # <<>>)
    /\ (rV' = [rV EXCEPT ![p] = Head(queue)])
    /\ (queue' = Tail(queue))
  \/ (* Dequeue from tail *)
    (queue # <<>>)
    /\ (rV' = [rV EXCEPT ![p] = Last(queue)])
    /\ (queue' = SubSeq(queue, 1, Len(queue) - 1))

=============================================================================