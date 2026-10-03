------------------------------- MODULE ConcurrentQueue -------------------------------

CONSTANTS Procs, Val, N

VARIABLES queue, rV

(*--algorithm ConcurrentQueue
variables queue = <<>>, rV \in [Procs -> {"okay", "full", "empty"} \cup Val \cup {NULL}];

process P \in Procs
begin
  while TRUE do
    either
      if queue /= <<>> then
        with v \in {queue[1], queue[len(queue)]} do
          rV[self] := v;
          queue := [IF v = queue[1] THEN Tail(queue) ELSE SubSeq(queue, 1, len(queue)-1)];
        endwith;
      else
        rV[self] := "empty";
      end if;
    or
      with v \in Val do
        if len(queue) < N then
          either
            queue := <<v>> \o queue;
          or
            queue := queue \o <<v>>;
          end either;
          rV[self] := "okay";
        else
          rV[self] := "full";
        end if;
      end with;
    end either;
  end while;
end process;

end algorithm*)

Spec ==
  /\ Init
  /\ [][Next]_<<queue, rV>>
  /\ WFQueueOps

Init ==
  /\ queue = << >>
  /\ rV \in [Procs -> {"okay", "full", "empty"} \cup Val \cup {NULL}]

Next ==
  \/ \E self \in Procs : Dequeue(self)
  \/ \E self \in Procs : Enqueue(self)

Dequeue(self) ==
  /\ queue /= << >>
  /\ \/ /\ rV' = [rV EXCEPT ![self] = queue[1]]
       /\ queue' = Tail(queue)
     \/ /\ rV' = [rV EXCEPT ![self] = queue[len(queue)]]
        /\ queue' = SubSeq(queue, 1, len(queue)-1)

Enqueue(self) ==
  /\ len(queue) < N
  /\ \/ /\ \E v \in Val : rV' = [rV EXCEPT ![self] = "okay"] /\ queue' = <<v>> \o queue
     \/ /\ \E v \in Val : rV' = [rV EXCEPT ![self] = "okay"] /\ queue' = queue \o <<v>>

WFQueueOps ==
  /\ WF_dequeue
  /\ WF_enqueue

WF_dequeue ==
  /\ \A self \in Procs :
     WF_<<queue, rV>>_(Dequeue(self))

WF_enqueue ==
  /\ \A self \in Procs :
     WF_<<queue, rV>>_(Enqueue(self))

StateConstraint ==
  len(queue) <= N

=============================================================================