---------------------------- MODULE ConcurrentQueue ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Val, Procs, N, null

ASSUME N \in Nat

(* --algorithm ConcurrentQueue
variables queue = << >>;

process P \in Procs
variable rV = null;
begin
  L: while TRUE do
       either
         with v \in Val do
           queue := <<v>> \o queue; rV := "okay"
         end with
       or
         with v \in Val do
           queue := queue \o <<v>>; rV := "okay"
         end with
       or
         await queue # << >>;
         rV := Head(queue); queue := Tail(queue)
       or
         await queue # << >>;
         rV := queue[Len(queue)]; queue := SubSeq(queue, 1, Len(queue) - 1)
       end either
     end while
end process
end algorithm *)

\* BEGIN TRANSLATION
VARIABLES queue, rV

vars == << queue, rV >>

ProcSet == Procs

RetVals == {"okay", "full", "empty", null} \cup Val

TypeOK ==
    /\ queue \in Seq(Val)
    /\ rV \in [Procs -> RetVals]

Init ==
    /\ queue = << >>
    /\ rV = [self \in Procs |-> null]

EnqFront(self) ==
    \E v \in Val :
        /\ queue' = <<v>> \o queue
        /\ rV' = [rV EXCEPT ![self] = "okay"]

EnqBack(self) ==
    \E v \in Val :
        /\ queue' = queue \o <<v>>
        /\ rV' = [rV EXCEPT ![self] = "okay"]

DeqHead(self) ==
    /\ queue # << >>
    /\ rV' = [rV EXCEPT ![self] = Head(queue)]
    /\ queue' = Tail(queue)

DeqTail(self) ==
    /\ queue # << >>
    /\ rV' = [rV EXCEPT ![self] = queue[Len(queue)]]
    /\ queue' = SubSeq(queue, 1, Len(queue) - 1)

P(self) ==
    \/ EnqFront(self)
    \/ EnqBack(self)
    \/ DeqHead(self)
    \/ DeqTail(self)

Next == \E self \in Procs : P(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(P(self))
\* END TRANSLATION

Constraint == Len(queue) <= N

=============================================================================