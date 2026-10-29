---------------------------- MODULE ConcurrentQueue ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Procs, Val, N

ASSUME N \in Nat

null == CHOOSE x : x \notin Val

(* --algorithm ConcurrentQueue
variables queue = << >>;
process (Proc \in Procs)
variables rV = null;
begin
P: while TRUE do
     either
       with v \in Val do
         either
           if Len(queue) < N then queue := <<v>> \o queue; rV := "okay";
           else rV := "full";
           end if;
         or
           if Len(queue) < N then queue := Append(queue, v); rV := "okay";
           else rV := "full";
           end if;
         end either;
       end with;
     or
       if queue # << >> then
         either
           rV := Head(queue); queue := Tail(queue);
         or
           rV := queue[Len(queue)]; queue := SubSeq(queue, 1, Len(queue) - 1);
         end either;
       else
         rV := "empty";
       end if;
     end either;
   end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES queue, pc, rV

vars == << queue, pc, rV >>

ProcSet == Procs

Init == /\ queue = << >>
        /\ rV = [self \in Procs |-> null]
        /\ pc = [self \in ProcSet |-> "P"]

EnqFront(self) ==
    \E v \in Val :
        IF Len(queue) < N
            THEN /\ queue' = <<v>> \o queue
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

Deq(self) ==
    IF queue # << >>
        THEN \/ /\ rV' = [rV EXCEPT ![self] = Head(queue)]
                /\ queue' = Tail(queue)
             \/ /\ rV' = [rV EXCEPT ![self] = queue[Len(queue)]]
                /\ queue' = SubSeq(queue, 1, Len(queue) - 1)
        ELSE /\ rV' = [rV EXCEPT ![self] = "empty"]
             /\ UNCHANGED queue

P(self) == /\ pc[self] = "P"
           /\ \/ EnqFront(self)
              \/ EnqBack(self)
              \/ Deq(self)
           /\ pc' = [pc EXCEPT ![self] = "P"]

Proc(self) == P(self)

Next == (\E self \in Procs : Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(P(self))
\* END TRANSLATION

-----------------------------------------------------------------------------
\* State constraint bounding the queue length
StateConstraint == Len(queue) <= N

\* Safety invariants
TypeOK ==
    /\ queue \in Seq(Val)
    /\ pc \in [ProcSet -> {"P"}]
    /\ rV \in [Procs -> Val \cup {"okay", "full", "empty", null}]

BoundedQueue == Len(queue) <= N

=============================================================================