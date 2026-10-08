------------------------------- MODULE ConcurrentQueue -------------------------------

CONSTANTS N, Val

VARIABLES queue, result, pc

(* --algorithm ConcurrentQueue
variables queue = <<>>, result = "", pc = [p \in Procs |-> "enqueue_back"];

process p \in Procs
begin
  while TRUE do
    either
      /\ pc[p] = "enqueue_back"
      /\ if Len(queue) < N then
           /\ queue' = Append(queue, CHOOSE v \in Val: TRUE)
           /\ result' = "success"
         else
           /\ result' = "full"
         fi
      /\ pc'[p] = "enqueue_front"
    or
      /\ pc[p] = "enqueue_front"
      /\ if Len(queue) < N then
           /\ queue' = <<CHOOSE v \in Val: TRUE>> \o queue
           /\ result' = "success"
         else
           /\ result' = "full"
         fi
      /\ pc'[p] = "dequeue_front"
    or
      /\ pc[p] = "dequeue_front"
      /\ if Len(queue) > 0 then
           /\ result' = Head(queue)
           /\ queue' = Tail(queue)
         else
           /\ result' = "empty"
         fi
      /\ pc'[p] = "dequeue_back"
    or
      /\ pc[p] = "dequeue_back"
      /\ if Len(queue) > 0 then
           /\ result' = Last(queue)
           /\ queue' = SubSeq(queue, 1, Len(queue)-1)
         else
           /\ result' = "empty"
         fi
      /\ pc'[p] = "enqueue_back"
    or
      /\ pc[p] \in {"enqueue_front", "dequeue_front", "dequeue_back"}
      /\ result' = ""
      /\ pc'[p] = pc[p]
    end either;
  od;
end process;

fairness <>[] <<\A p \in Procs: <>[](pc[p] = "enqueue_back")>>;
fairness <>[] <<\A p \in Procs: <>[](pc[p] = "enqueue_front")>>;
fairness <>[] <<\A p \in Procs: <>[](pc[p] = "dequeue_front")>>;
fairness <>[] <<\A p \in Procs: <>[](pc[p] = "dequeue_back")>>;

Spec == /\ Init
        /\ SF_<<Procs>>
        /\ WF_<<Procs>>

Init == /\ queue = << >>
        /\ result = ""
        /\ pc \in [Procs -> {"enqueue_front", "enqueue_back", "dequeue_front", "dequeue_back"}]

Next ==
  \/ \E p \in Procs: \A q \in Procs \ {p}: /\ pc' = [pc EXCEPT ![p] = pc'[p]]
                                               /\ queue' = queue
                                               /\ result' = result
                                               /\ q \notin DOMAIN pc'
  \/ \E p \in Procs: /\ pc' = [pc EXCEPT ![p] = pc'[p]]
                      /\ queue' = queue'
                      /\ result' = result'
                      /\ UNCHANGED <<Procs - {p}>> 

Spec == Spec

=============================================================================