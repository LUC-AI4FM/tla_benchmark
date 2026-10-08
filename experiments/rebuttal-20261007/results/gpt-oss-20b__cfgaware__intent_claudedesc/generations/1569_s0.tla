------------------------------ MODULE Bakery ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumProcs, MaxNum

VARIABLES choosing, ticket, inCS

(* ------------------------------------------------------------------ *)
(* Initial state *)
Init ==
    /\ choosing = [i \in 1..NumProcs |-> FALSE]
    /\ ticket   = [i \in 1..NumProcs |-> 0]
    /\ inCS     = {}

(* ------------------------------------------------------------------ *)
(* Helper: set of other processes that are not choosing *)
Others(i) == {j \in 1..NumProcs \ {i} : NOT choosing[j]}

(* Max ticket among the others (used only inside ChooseTicket) *)
MaxTicket(i) ==
    IF Others(i) = {} THEN
        0
    ELSE
        MAX(Seq({ticket[j] : j \in Others(i)}))

(* ------------------------------------------------------------------ *)
(* Condition that allows process i to enter the critical section *)
WaitCondition(i) ==
    \A j \in 1..NumProcs :
        j /= i =>
            (ticket[j] = 0 \/ ticket[j] > ticket[i] \/ (ticket[j] = ticket[i] /\ j > i))

(* ------------------------------------------------------------------ *)
(* Actions *)

StartChoosing(i) ==
    /\ i \in 1..NumProcs
    /\ ticket[i] = 0
    /\ NOT (i \in inCS)
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<ticket, inCS>>

ChooseTicket(i) ==
    LET others == Others(i)
        maxT   == IF others = {} THEN 0 ELSE MAX(Seq({ticket[j] : j \in others}))
    IN
    /\ i \in 1..NumProcs
    /\ choosing[i] = TRUE
    /\ ticket[i] = 0
    /\ \A j \in 1..NumProcs : j /= i => NOT choosing[j]
    /\ maxT < MaxNum
    /\ ticket'   = [ticket EXCEPT ![i] = maxT + 1]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<inCS>>

EnterCS(i) ==
    /\ i \in 1..NumProcs
    /\ ticket[i] > 0
    /\ NOT (i \in inCS)
    /\ WaitCondition(i)
    /\ inCS'     = inCS \cup {i}
    /\ UNCHANGED <<choosing, ticket>>

ExitCS(i) ==
    /\ i \in 1..NumProcs
    /\ i \in inCS
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ ticket'   = [ticket   EXCEPT ![i] = 0]
    /\ inCS'     = inCS \ {i}

(* ------------------------------------------------------------------ *)
(* Next-state relation *)
Next ==
    \E i \in 1..NumProcs :
        StartChoosing(i) \/ ChooseTicket(i) \/ EnterCS(i) \/ ExitCS(i)

(* ------------------------------------------------------------------ *)
(* Specification *)
Spec == Init /\ [][Next]_<<choosing, ticket, inCS>>

(* ------------------------------------------------------------------ *)
(* Invariant: mutual exclusion and ticket bound *)
MutualExclusion ==
    CARDINALITY(inCS) <= 1

TicketBound ==
    \A i \in 1..NumProcs : ticket[i] <= MaxNum

Invariant == MutualExclusion /\ TicketBound
===============================================================================