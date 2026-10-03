---- MODULE ConcurrentQueue ----
EXTENDS Integers, Sequences, TLC

CONSTANTS Procs, Val, N
ASSUME N \in Nat /\ N > 0

VARIABLES queue, rV, pc

vars == <<queue, rV, pc>>

(* The set of possible return values for a process. *)
ReturnVals == {"okay", "full", "empty", "null"} \cup Val

(* Type invariant for the state variables. *)
TypeOK ==
    /\ queue \in Seq(Val)
    /\ rV \in [Procs -> ReturnVals]
    /\ pc \in [Procs -> {"Loop"}]

(*
--algorithm ConcurrentQueue
variables
  queue = <<>>,
  rV = [p \in Procs |-> "null"];

process (p \in Procs)
variable op;
begin
Loop:
  while TRUE do
    either
      with v \in Val do
        if Len(self.queue) < N then
          self.queue := <<v>> \o self.queue;
          self.rV[self.p] := "okay";
        else
          self.rV[self.p] := "full";
        end if;
      end with;
    or
      with v \in Val do
        if Len(self.queue) < N then
          self.queue := Append(self.queue, v);
          self.rV[self.p] := "okay";
        else
          self.rV[self.p] := "full";
        end if;
      end with;
    or
      if Len(self.queue) > 0 then
        self.rV[self.p] := Head(self.queue);
        self.queue := Tail(self.queue);
      else
        self.rV[self.p] := "empty";
      end if;
    or
      if Len(self.queue) > 0 then
        self.rV[self.p] := self.queue[Len(self.queue)];
        self.queue := SubSeq(self.queue, 1, Len(self.queue) - 1);
      else
        self.rV[self.p] := "empty";
      end if;
    end either;
  end while;
end process;
end algorithm;
*)

\* The initial state of the system.
Init ==
    /\ queue = <<>>
    /\ rV = [p \in Procs |-> "null"]
    /\ pc = [p \in Procs |-> "Loop"]

\* An action by process `self`. It can non-deterministically choose one of four
\* operations: enqueue to front, enqueue to back, dequeue from head, or dequeue from tail.
P(self) ==
    /\ pc[self] = "Loop"
    /\ \/ (* Enqueue Front *)
          (\E v \in Val :
              IF Len(queue) < N
              THEN /\ queue' = <<v>> \o queue
                   /\ rV' = [rV EXCEPT ![self] = "okay"]
              ELSE /\ queue' = queue
                   /\ rV' = [rV EXCEPT ![self] = "full"])
       \/ (* Enqueue Back *)
          (\E v \in Val :
              IF Len(queue) < N
              THEN /\ queue' = Append(queue, v)
                   /\ rV' = [rV EXCEPT ![self] = "okay"]
              ELSE /\ queue' = queue
                   /\ rV' = [rV EXCEPT ![self] = "full"])
       \/ (* Dequeue Head *)
          (IF Len(queue) > 0
           THEN /\ queue' = Tail(queue)
                /\ rV' = [rV EXCEPT ![self] = Head(queue)]
           ELSE /\ queue' = queue
                /\ rV' = [rV EXCEPT ![self] = "empty"])
       \/ (* Dequeue Tail *)
          (IF Len(queue) > 0
           THEN LET q_len == Len(queue) IN
                /\ queue' = SubSeq(queue, 1, q_len - 1)
                /\ rV' = [rV EXCEPT ![self] = queue[q_len]]
           ELSE /\ queue' = queue
                /\ rV' = [rV EXCEPT ![self] = "empty"])
    /\ pc' = [pc EXCEPT ![self] = "Loop"]

\* The next-state relation. A step consists of one process performing an action.
Next == \E self \in Procs : P(self)

\* The complete temporal specification, stating that the system starts in Init
\* and always takes steps defined by Next (or stutters).
Spec == Init /\ [][Next]_vars

\* A state constraint (safety invariant) that the queue length is bounded by N.
QueueBound == Len(queue) <= N

\* The liveness property: weak fairness for each process's action.
\* This ensures that if a process is continuously able to take a step, it
\* must eventually do so.
Fairness == \A self \in Procs : WF_vars(P(self))

=============================================================================