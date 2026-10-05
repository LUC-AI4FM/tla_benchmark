---------------------------- MODULE TerminationDetection ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS 
    N,              \* Number of processes (fixed finite set)
    MaxMessages     \* Maximum number of in-transit messages per process (for model checking)

ASSUME N \in Nat /\ N > 0
ASSUME MaxMessages \in Nat /\ MaxMessages > 0

Procs == 0..(N-1)

VARIABLES
    active,         \* Function: Procs -> BOOLEAN, whether each process is active
    pending,        \* Function: Procs -> Nat, number of in-transit messages to each process
    detected        \* Boolean: whether termination has been detected

vars == <<active, pending, detected>>

\* Type invariant for model checking
TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ pending \in [Procs -> Nat]
    /\ \A p \in Procs : pending[p] <= MaxMessages
    /\ detected \in BOOLEAN

\* Global termination: all processes inactive and no messages in transit
Terminated ==
    /\ \A p \in Procs : ~active[p]
    /\ \A p \in Procs : pending[p] = 0

\* Initial state: all processes active, no messages in transit, not detected
Init ==
    /\ active = [p \in Procs |-> TRUE]
    /\ pending = [p \in Procs |-> 0]
    /\ detected = FALSE

\* An active process p sends a message to process q
\* Bounded by MaxMessages for model checking
Send(p, q) ==
    /\ active[p]
    /\ pending[q] < MaxMessages
    /\ ~detected
    /\ pending' = [pending EXCEPT ![q] = @ + 1]
    /\ UNCHANGED <<active, detected>>

\* Process p receives a message; reactivates if inactive
Receive(p) ==
    /\ pending[p] > 0
    /\ ~detected
    /\ pending' = [pending EXCEPT ![p] = @ - 1]
    /\ active' = [active EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<detected>>

\* An active process p voluntarily becomes inactive
Deactivate(p) ==
    /\ active[p]
    /\ ~detected
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<pending, detected>>

\* Termination detection: can only occur when termination actually holds
Detect ==
    /\ Terminated
    /\ ~detected
    /\ detected' = TRUE
    /\ UNCHANGED <<active, pending>>

\* Combined next-state relation
Next ==
    \/ \E p \in Procs : \E q \in Procs : Send(p, q)
    \/ \E p \in Procs : Receive(p)
    \/ \E p \in Procs : Deactivate(p)
    \/ Detect

\* Fairness: weak fairness on all actions to ensure progress
\* This allows detection to be delayed but eventually must happen
Fairness ==
    /\ \A p \in Procs : \A q \in Procs : WF_vars(Send(p, q))
    /\ \A p \in Procs : WF_vars(Receive(p))
    /\ \A p \in Procs : WF_vars(Deactivate(p))
    /\ WF_vars(Detect)

\* Full specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* =============================================================================