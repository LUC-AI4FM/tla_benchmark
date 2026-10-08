```tla
---------------------------- MODULE DequeSpec ----------------------------

CONSTANTS Procs, Val, N

VARIABLES queue, rV

(*--algorithm deque_spec

variables queue = <<>>, rV = [p \in Procs |-> null];

process (p \in Procs)
begin
L1:
  either
    /\ \/ /\ queue' = Append(queue, CHOOSE v \in Val: TRUE)
       \/ /\ queue' = Prepend(CHOOSE v \in Val: TRUE, queue)
       \/ /\ queue' = queue
          /\ rV' = "full"
  or
    if queue # <<>> then
      either
        /\ queue' = Tail(queue)
           /\ rV' = Head(queue)
      or
        /\ queue' = Front(queue)
           /\ rV' = Last(queue)
      else
        /\ queue' = queue
           /\ rV' = "empty"
  end either;
L2:
  rV' = [rV EXCEPT ![p] = null];
  goto L1;
end process;

fairness  \A p \in Procs: WF_(pc[p], {L1, L2})

end algorithm*)

Spec == /\ Init
        /\ \A p \in Procs: SpecProc(p)
        /\ QueueLenBound

Init == /\ queue = <<>>
      /\ rV = [p \in Procs |-> null]

SpecProc(p) ==
  \/ pc[p] = "L1" /\ L1Action(p)
  \/ pc[p] = "L2" /\ L2Action(p)

L1Action(p) ==
  \/ /\ queue' = Append(queue, CHOOSE v \in Val: TRUE)
     \/ rV' = [rV EXCEPT ![p] = null]
  \/ /\ queue' = Prepend(CHOOSE v \in Val: TRUE, queue)
     \/ rV' = [rV EXCEPT ![p] = null]
  \/ /\ queue' = queue
     /\ rV' = [rV EXCEPT ![p] = "full"]
  \/ /\ queue # <<>>
     /\ (queue' = Tail(queue) /\ rV' = [rV EXCEPT ![p] = Head(queue)])
        \/ (queue' = Front(queue) /\ rV' = [rV EXCEPT ![p] = Last(queue)])
  \/ /\ queue = <<>>
     /\ rV' = [rV EXCEPT ![p] = "empty"]

L2Action(p) ==
  /\ rV' = [rV EXCEPT ![p] = null]
  /\ pc'[p] = "L1"

QueueLenBound == Len(queue) \leq N

Append(seq, elem) == seq \o <<elem>>

Prepend(elem, seq) == <<elem>> \o seq

Head(seq) == seq[1]

Tail(seq) == SubSeq(seq, 2, Len(seq))

Front(seq) == SubSeq(seq, 1, Len(seq) - 1)

Last(seq) == seq[Len(seq)]

SubSeq(seq, start, end) ==
  <<seq[i] : i \in start..end>>

==

```

This TLA+ specification models the described system with a shared queue and per-process local variables. It includes the necessary definitions for `Spec` and `Val`, ensuring it binds to the specified model-checking configuration.