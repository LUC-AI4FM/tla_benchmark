------------------------------- MODULE ConcurrentIncrement -------------------------------
EXTENDS Naturals

CONSTANTS Process1, Process2

VARIABLES x, pc

Init == /\ x = 0
        /\ pc = [Process1 -> "start", Process2 -> "start"]

Next ==
    \/ /\ pc[Process1] = "start"
       /\ pc' = [pc EXCEPT ![Process1] = "increment"]
       /\ x' = x + 1
       /\ UNCHANGED pc[Process2]
    \/ /\ pc[Process1] = "increment"
       /\ pc' = [pc EXCEPT ![Process1] = "done"]
       /\ UNCHANGED x
       /\ UNCHANGED pc[Process2]
    \/ /\ pc[Process2] = "start"
       /\ pc' = [pc EXCEPT ![Process2] = "increment"]
       /\ x' = x + 1
       /\ UNCHANGED pc[Process1]
    \/ /\ pc[Process2] = "increment"
       /\ pc' = [pc EXCEPT ![Process2] = "done"]
       /\ UNCHANGED x
       /\ UNCHANGED pc[Process1]

Spec == Init /\ [][Next]_<<x, pc>>

Termination ==
    <>[](pc[Process1] = "done" /\ pc[Process2] = "done")

WF_Process1 == WF_next(pc[Process1], {"start", "increment", "done"})
WF_Process2 == WF_next(pc[Process2], {"start", "increment", "done"})

Fairness ==
    WF_Process1 /\ WF_Process2

CompleteSpec == Spec /\ Fairness /\ Termination
=============================================================================