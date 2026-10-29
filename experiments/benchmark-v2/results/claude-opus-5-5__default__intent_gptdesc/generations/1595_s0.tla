---------------------------- MODULE FairCounterLoop ----------------------------
EXTENDS Naturals

CONSTANT Bound

ASSUME BoundAssumption == Bound \in Nat /\ Bound > 0

VARIABLES counter, pc

vars == <<counter, pc>>

States == {"loop", "done"}

TypeOK ==
    /\ counter \in 0..Bound
    /\ pc \in States

Init ==
    /\ counter = 0
    /\ pc = "loop"

(* Loop body: increment the shared counter by exactly one while below the bound *)
Increment ==
    /\ pc = "loop"
    /\ counter < Bound
    /\ counter' = counter + 1
    /\ UNCHANGED pc

(* Loop exit: once the bound is reached, move to the terminated state *)
Finish ==
    /\ pc = "loop"
    /\ counter >= Bound
    /\ pc' = "done"
    /\ UNCHANGED counter

(* Idle after termination: stuttering, so termination is not deadlock *)
Terminated ==
    /\ pc = "done"
    /\ UNCHANGED vars

Step == Increment \/ Finish

Next == Step \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Safety properties *)

(* The counter never decreases and never skips values *)
MonotonicStep ==
    [][ \/ counter' = counter
        \/ counter' = counter + 1 ]_vars

(* Any change of the counter is an increment by exactly one, performed in the loop *)
IncrementOnlyInLoop ==
    [][ counter' /= counter => (pc = "loop" /\ counter < Bound /\ counter' = counter + 1) ]_vars

(* Once terminated, the process stays terminated and the counter stays fixed *)
TerminationStable ==
    [][ pc = "done" => (pc' = "done" /\ counter' = counter) ]_vars

(* Counter never exceeds the bound *)
BoundRespected == counter <= Bound

(* Terminated state implies counter equals the bound *)
DoneImpliesBound == (pc = "done") => (counter = Bound)

-----------------------------------------------------------------------------
(* Liveness properties *)

(* Progress/termination: the process eventually terminates with counter = Bound *)
Termination == <>(pc = "done" /\ counter = Bound)

(* Stays terminated forever once terminated *)
EventuallyAlwaysDone == <>[](pc = "done")

(* Liveness checkpoint: the counter takes an intermediate value (e.g., 5) *)
Midpoint == IF Bound >= 5 THEN 5 ELSE Bound \div 2

ReachesIntermediate == <>(counter = Midpoint)

(* Liveness checkpoint: the transition from Bound-1 to Bound occurs as one atomic step *)
FinalStepOccurs == <><<counter = Bound - 1 /\ counter' = Bound>>_vars

(* Progress from any loop state: continuously enabled increments eventually happen *)
Progress == \A k \in 0..(Bound - 1) : (counter = k) ~> (counter = k + 1)

=============================================================================