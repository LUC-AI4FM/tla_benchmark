---------------------------- MODULE ConcurrentQueue ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Procs, Val, N, null

ASSUME /\ N \in Nat
       /\ null \notin Val
       /\ Procs # {}

(* --algorithm ConcurrentQueue
variables queue = << >>;

process P \in Procs
variables rV = null;
begin
  Loop:
    while TRUE do
      either
        with v \in Val do
          if Len(queue) < N then queue := << v >> \o queue; rV := "okay";
          else rV := "full";
          end if;
        end with;
      or
        with v \in Val do
          if Len(queue) < N then queue := Append(queue, v); rV := "okay";
          else rV := "full";
          end if;
        end with;
      or
        if queue # << >> then rV := Head(queue); queue := Tail(queue);
        else rV := "empty";
        end if;
      or
        if queue # << >> then rV := queue[Len(queue)];
                              queue := SubSeq(queue, 1, Len(queue) - 1);
        else rV := "empty";
        end if;
      end either;
    end while;
end process;
end algorithm *)

\* BEGIN TRANSLATION
VARIABLES queue, pc, rV

vars == << queue, pc, rV >>

ProcSet == Procs

Init == /\ queue = << >>
        /\ rV = [self \in Procs |-> null]
        /\ pc = [self \in ProcSet |-> "Loop"]

EnqFront(self) ==
    \E v \in Val :
        IF Len(queue) < N
           THEN /\ queue' = << v >> \o queue
                /\ rV' = [rV EXCEPT ![self] = "okay"]
           ELSE /\ rV' = [rV EXCEPT ![self] = "full"]
                /\ UNCHANGED queue

EnqBack(self) ==
    \E v \in Val :
        IF Len(queue) < N
           THEN /\ queue' = Append(queue, v)
                /\ rV' = [rV EXCEPT ![self] = "okay"]
           ELSE /\ rV' = [rV EXCEPT ![self] = "full"]
                /\ UNCHANGED queue

DeqHead(self) ==
    IF queue # << >>
       THEN /\ rV' = [rV EXCEPT ![self] = Head(queue)]
            /\ queue' = Tail(queue)
       ELSE /\ rV' = [rV EXCEPT ![self] = "empty"]
            /\ UNCHANGED queue

DeqTail(self) ==
    IF queue # << >>
       THEN /\ rV' = [rV EXCEPT ![self] = queue[Len(queue)]]
            /\ queue' = SubSeq(queue, 1, Len(queue) - 1)
       ELSE /\ rV' = [rV EXCEPT ![self] = "empty"]
            /\ UNCHANGED queue

Loop(self) == /\ pc[self] = "Loop"
              /\ \/ EnqFront(self)
                 \/ EnqBack(self)
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
    /\ rV \in [Procs -> Val \cup {"okay", "full", "empty", null}]
    /\ pc \in [ProcSet -> {"Loop"}]

BoundedQueue == Len(queue) <= N

\* Liveness: every process keeps taking steps
ProgressLiveness == \A self \in Procs : []<>(ENABLED P(self) => <><<P(self)>>_vars)
=============================================================================