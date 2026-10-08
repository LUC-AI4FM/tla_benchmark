------------------------------- MODULE AsyncTerminationDetection -------------------------------

CONSTANTS N \* Number of processes

VARIABLES 
    active, \* Set of active processes
    messages, \* Messages in transit, a function from process to set of messages
    terminationDetected \* Boolean indicating if termination has been detected

ASSUME N \in Nat /\ N > 0

\* Initial state: all processes are active and no messages are in transit
Init == 
    /\ active = {1..N}
    /\ messages = [p \in 1..N |-> {}]
    /\ terminationDetected = FALSE

\* Action: a process sends a message to another process
Send(p, q, msg) ==
    /\ p \in active
    /\ q \in 1..N
    /\ q # p
    /\ messages' = [messages EXCEPT ![p] = messages[p] \ {msg}, ![q] = messages[q] \cup {msg}]
    /\ UNCHANGED <<active, terminationDetected>>

\* Action: a process receives a message and becomes active if it was inactive
Receive(p, msg) ==
    /\ p \in 1..N
    /\ msg \in messages[p]
    /\ messages' = [messages EXCEPT ![p] = messages[p] \ {msg}]
    /\ active' = active \cup {p}
    /\ UNCHANGED terminationDetected

\* Action: a process voluntarily becomes inactive if it has no local work
Deactivate(p) ==
    /\ p \in active
    /\ messages[p] = {}
    /\ active' = active \ {p}
    /\ UNCHANGED messages
    /\ UNCHANGED terminationDetected

\* Action: the system detects global termination if all processes are inactive and no messages are in transit
Detect() ==
    /\ active = {}
    /\ (\A p \in 1..N : messages[p] = {})
    /\ terminationDetected' = TRUE
    /\ UNCHANGED <<active, messages>>

\* Next-state relation: any of the actions can occur
Next == 
    \/ (\E p, q \in 1..N, msg \in Msgs : Send(p, q, msg))
    \/ (\E p \in 1..N, msg \in Msgs : Receive(p, msg))
    \/ (\E p \in 1..N : Deactivate(p))
    \/ Detect()

\* Specification: initial state and next-state relation
Spec == Init /\ [][Next]_<<active, messages, terminationDetected>>

\* Invariants

\* Safety: the detector may never claim termination unless global termination actually holds.
Safety ==
    ~terminationDetected \/ (active = {} /\ (\A p \in 1..N : messages[p] = {}))

\* Quiescence/stability: once global termination holds, it remains true thereafter.
Quiescence ==
    [](active = {} /\ (\A p \in 1..N : messages[p] = {}) => <>(terminationDetected))

\* Liveness: if the system reaches a state of global termination, the detector must eventually set the detection predicate true.
Liveness ==
    <>(active = {} /\ (\A p \in 1..N : messages[p] = {})) ~> <>(terminationDetected)

\* Type and boundedness constraints suitable for model checking
TypeOK ==
    /\ active \subseteq (1..N)
    /\ terminationDetected \in BOOLEAN
    /\ (\A p \in 1..N : messages[p] \subseteq Msgs)
    /\ (\A p \in 1..N : Cardinality(messages[p]) \leq MaxMsgs)

\* Define the set of possible messages and a bound on message counts per process for exploration
CONSTANTS Msgs, MaxMsgs

ASSUME Msgs \in SUBSET STRING
ASSUME MaxMsgs \in Nat /\ MaxMsgs > 0

THEOREM Spec => []TypeOK /\ []Safety /\ []Quiescence /\ <>Liveness

=============================================================================