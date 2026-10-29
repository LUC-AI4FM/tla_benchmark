---------------------------- MODULE ConcurrentQueue ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Procs, Val, N, null

ASSUME /\ N \in Nat
       /\ null \notin Val

(* --algorithm ConcurrentQueue
variables queue = << >>;
process P \in Procs
variables rV = null;
begin
  Loop:
    while TRUE do
      either
        with v \in Val do
          either queue := Append(queue, v) ;
          or     queue := <<v>> \o queue ;
          end either;
          rV := "okay";
        end with;
      or
        await queue # << >>;
        either rV := Head(queue); queue := Tail(queue);
        or     rV := queue[Len(queue)];
               queue := SubSeq(queue, 1, Len(queue) - 1);
        end either;
      end either;
    end while;
end process
end algorithm *)

\* BEGIN TRANSLATION
VARIABLES queue, pc, rV

vars == << queue, pc, rV >>

ProcSet == Procs

RetVals == {"okay", "full", "empty", null} \cup Val

Init == /\ queue = << >>
        /\ rV = [self \in Procs |-> null]
        /\ pc = [self \in ProcSet |-> "Loop"]

EnqBack(self) ==
    \E v \in Val :
        /\ queue' = Append(queue, v)
        /\ rV' = [rV EXCEPT ![self] = "okay"]

EnqFront(self) ==
    \E v \in Val :
        /\ queue' = <<v>> \o queue
        /\ rV' = [rV EXCEPT ![self] = "okay"]

DeqHead(self) ==
    /\ queue # << >>
    /\ rV' = [rV EXCEPT ![self] = Head(queue)]
    /\ queue' = Tail(queue)

DeqTail(self) ==
    /\ queue # << >>
    /\ rV' = [rV EXCEPT ![self] = queue[Len(queue)]]
    /\ queue' = SubSeq(queue, 1, Len(queue) - 1)

Loop(self) ==
    /\ pc[self] = "Loop"
    /\ \/ EnqBack(self)
       \/ EnqFront(self)
       \/ DeqHead(self)
       \/ DeqTail(self)
    /\ pc' = [pc EXCEPT ![self] = "Loop"]

P(self) == Loop(self)

Next == (\E self \in Procs : P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(P(self))
\* END TRANSLATION

-----------------------------------------------------------------------------
\* State constraint bounding the queue length (for model checking)
QueueConstraint == Len(queue) <= N

\* Safety invariants
TypeOK ==
    /\ queue \in Seq(Val)
    /\ rV \in [Procs -> RetVals]
    /\ pc \in [ProcSet -> {"Loop"}]

QueueBounded == Len(queue) <= N + 1

\* Liveness: every process keeps taking steps (always enabled enqueue)
Progress == \A self \in Procs : []<>(<<P(self)>>_vars)
=============================================================================