---------------------------- MODULE ConcurrentQueue ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Procs, Val, N, null

ASSUME /\ N \in Nat
       /\ null \notin Val
       /\ null \notin {"okay", "full", "empty"}

(* --algorithm ConcurrentQueue
variables queue = << >>;

process (P \in Procs)
variable rV = null;
begin
P:
  while TRUE do
    either
      with v \in Val do
        if Len(queue) < N then
          queue := << v >> \o queue; rV := "okay"
        else
          rV := "full"
        end if
      end with
    or
      with v \in Val do
        if Len(queue) < N then
          queue := Append(queue, v); rV := "okay"
        else
          rV := "full"
        end if
      end with
    or
      if queue /= << >> then
        rV := Head(queue); queue := Tail(queue)
      else
        rV := "empty"
      end if
    or
      if queue /= << >> then
        rV := queue[Len(queue)]; queue := SubSeq(queue, 1, Len(queue) - 1)
      else
        rV := "empty"
      end if
    end either
  end while
end process
end algorithm *)

\* BEGIN TRANSLATION
VARIABLES queue, rV

vars == << queue, rV >>

ProcSet == Procs

RetVals == {"okay", "full", "empty", null} \cup Val

Init == /\ queue = << >>
        /\ rV = [self \in Procs |-> null]

EnqFront(self) ==
    \E v \in Val :
        IF Len(queue) < N
        THEN /\ queue' = << v >> \o queue
             /\ rV' = [rV EXCEPT ![self] = "okay"]
        ELSE /\ rV' = [rV EXCEPT ![self] = "full"]
             /\ queue' = queue

EnqBack(self) ==
    \E v \in Val :
        IF Len(queue) < N
        THEN /\ queue' = Append(queue, v)
             /\ rV' = [rV EXCEPT ![self] = "okay"]
        ELSE /\ rV' = [rV EXCEPT ![self] = "full"]
             /\ queue' = queue

DeqHead(self) ==
    IF queue /= << >>
    THEN /\ rV' = [rV EXCEPT ![self] = Head(queue)]
         /\ queue' = Tail(queue)
    ELSE /\ rV' = [rV EXCEPT ![self] = "empty"]
         /\ queue' = queue

DeqTail(self) ==
    IF queue /= << >>
    THEN /\ rV' = [rV EXCEPT ![self] = queue[Len(queue)]]
         /\ queue' = SubSeq(queue, 1, Len(queue) - 1)
    ELSE /\ rV' = [rV EXCEPT ![self] = "empty"]
         /\ queue' = queue

P(self) == \/ EnqFront(self)
           \/ EnqBack(self)
           \/ DeqHead(self)
           \/ DeqTail(self)

Next == \E self \in Procs : P(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(P(self))
\* END TRANSLATION

\* State constraint bounding the queue length
StateConstraint == Len(queue) <= N

\* Safety invariants
TypeOK == /\ queue \in Seq(Val)
          /\ rV \in [Procs -> RetVals]

BoundedQueue == Len(queue) <= N

=============================================================================