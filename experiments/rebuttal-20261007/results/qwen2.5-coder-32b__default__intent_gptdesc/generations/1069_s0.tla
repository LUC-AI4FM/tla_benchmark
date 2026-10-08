------------------------------- MODULE AsyncTerminationDetection -------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS N \* Number of processes
ASSUME N > 0

VARIABLES 
    active,       \* Set of active processes
    messages,     \* Messages in transit: [p \in 1..N -> Nat]
    detected      \* Global termination detection flag

Init == /\ active = {1..N}
        /\ messages = [p \in 1..N |-> 0]
        /\ detected = FALSE

Next ==
    \/ \E p \in active : 
        \E q \in 1..N \ {p} :
            /\ messages' = [messages EXCEPT ![q] = messages[q] + 1]
            /\ UNCHANGED <<active, detected>>
    \/ \E p \in 1..N :
        /\ messages[p] > 0
        /\ active' = active \cup {p}
        /\ messages' = [messages EXCEPT ![p] = messages[p] - 1]
        /\ UNCHANGED detected
    \/ \E p \in active :
        /\ active' = active \ {p}
        /\ UNCHANGED <<messages, detected>>
    \/ /\ detected = FALSE
       /\ global_termination
       /\ detected' = TRUE
       /\ UNCHANGED <<active, messages>>

global_termination == (active = {}) /\ (FORALL p \in 1..N : messages[p] = 0)

Spec ==
    /\ Init
    /\ [][Next]_<<active, messages, detected>>
    /\ WF_[Next]_<<active, messages, detected>>

\* Safety: the detector may never claim termination unless global termination actually holds.
Safety == [](detected => global_termination)

\* Liveness: if the system reaches a state of global termination, the detector must eventually set the detection predicate true.
Liveness == <>(global_termination => <>detected)

\* Quiescence/stability: once global termination holds, it remains true thereafter (no actions can revive processes or reintroduce messages).
Quiescence == [](global_termination => []global_termination)

\* Type and boundedness constraints suitable for model checking
TypeOK ==
    /\ active \subseteq (1..N)
    /\ detected \in BOOLEAN
    /\ (\A p \in 1..N : messages[p] \in Nat)

BoundedMessages == 
    \A p \in 1..N : messages[p] <= N

CompleteSpec == Spec /\ TypeOK /\ BoundedMessages /\ Safety /\ Liveness /\ Quiescence

================================================================================================