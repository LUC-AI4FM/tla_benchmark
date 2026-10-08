---------------------------- MODULE Bakery ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    NumProcs,      \* Number of processes
    MaxTicket      \* Maximum ticket value for state-space bounding

ASSUME NumProcs \in Nat /\ NumProcs > 0
ASSUME MaxTicket \in Nat /\ MaxTicket > 0

Procs == 1..NumProcs

VARIABLES
    pc,           \* Program counter for each process
    choosing,     \* Boolean flag: TRUE when process is selecting a ticket
    ticket,       \* Ticket number for each process (0 means not in queue)
    maxRead,      \* Maximum ticket read so far during doorway phase
    toRead,       \* Set of processes still to read during doorway phase
    toCheck       \* Set of processes still to check during waiting phase

vars == <<pc, choosing, ticket, maxRead, toRead, toCheck>>

\* Program counter states:
\* "idle"     - not trying to enter critical section
\* "doorway"  - reading tickets from other processes
\* "assign"   - assigning ticket
\* "waiting"  - waiting for turn
\* "cs"       - in critical section

TypeOK ==
    /\ pc \in [Procs -> {"idle", "doorway", "assign", "waiting", "cs"}]
    /\ choosing \in [Procs -> BOOLEAN]
    /\ ticket \in [Procs -> 0..MaxTicket]
    /\ maxRead \in [Procs -> 0..MaxTicket]
    /\ toRead \in [Procs -> SUBSET Procs]
    /\ toCheck \in [Procs -> SUBSET Procs]

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ choosing = [p \in Procs |-> FALSE]
    /\ ticket = [p \in Procs |-> 0]
    /\ maxRead = [p \in Procs |-> 0]
    /\ toRead = [p \in Procs |-> {}]
    /\ toCheck = [p \in Procs |-> {}]

\* Process p starts trying to enter critical section
StartDoorway(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "doorway"]
    /\ choosing' = [choosing EXCEPT ![p] = TRUE]
    /\ maxRead' = [maxRead EXCEPT ![p] = 0]
    /\ toRead' = [toRead EXCEPT ![p] = Procs \ {p}]
    /\ UNCHANGED <<ticket, toCheck>>

\* Process p reads ticket from another process q during doorway phase
ReadTicket(p) ==
    /\ pc[p] = "doorway"
    /\ toRead[p] /= {}
    /\ \E q \in toRead[p]:
        /\ choosing[q] = FALSE  \* Wait until q is not choosing
        /\ toRead' = [toRead EXCEPT ![p] = @ \ {q}]
        /\ maxRead' = [maxRead EXCEPT ![p] = IF ticket[q] > maxRead[p] 
                                             THEN ticket[q] 
                                             ELSE maxRead[p]]
    /\ UNCHANGED <<pc, choosing, ticket, toCheck>>

\* Process p finishes doorway phase and assigns ticket
AssignTicket(p) ==
    /\ pc[p] = "doorway"
    /\ toRead[p] = {}
    /\ pc' = [pc EXCEPT ![p] = "assign"]
    /\ UNCHANGED <<choosing, ticket, maxRead, toRead, toCheck>>

\* Process p actually takes the ticket and prepares to wait
TakeTicket(p) ==
    /\ pc[p] = "assign"
    /\ ticket' = [ticket EXCEPT ![p] = maxRead[p] + 1]
    /\ choosing' = [choosing EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ toCheck' = [toCheck EXCEPT ![p] = Procs \ {p}]
    /\ UNCHANGED <<maxRead, toRead>>

\* Process p checks another process q during waiting phase
\* A process p has priority over q if:
\*   - q has ticket 0 (not competing), OR
\*   - p's ticket is smaller, OR
\*   - tickets are equal but p has smaller ID
CheckProcess(p) ==
    /\ pc[p] = "waiting"
    /\ toCheck[p] /= {}
    /\ \E q \in toCheck[p]:
        /\ choosing[q] = FALSE  \* Wait until q is not choosing
        /\ \/ ticket[q] = 0     \* q is not competing
           \/ ticket[p] < ticket[q]  \* p has smaller ticket
           \/ (ticket[p] = ticket[q] /\ p < q)  \* tie-breaker: smaller ID wins
        /\ toCheck' = [toCheck EXCEPT ![p] = @ \ {q}]
    /\ UNCHANGED <<pc, choosing, ticket, maxRead, toRead>>

\* Process p enters critical section after checking all processes
EnterCS(p) ==
    /\ pc[p] = "waiting"
    /\ toCheck[p] = {}
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED <<choosing, ticket, maxRead, toRead, toCheck>>

\* Process p exits critical section
ExitCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ UNCHANGED <<choosing, maxRead, toRead, toCheck>>

\* Next state relation
Next ==
    \E p \in Procs:
        \/ StartDoorway(p)
        \/ ReadTicket(p)
        \/ AssignTicket(p)
        \/ TakeTicket(p)
        \/ CheckProcess(p)
        \/ EnterCS(p)
        \/ ExitCS(p)

\* Fairness: weak fairness for all process actions
Fairness ==
    \A p \in Procs:
        /\ WF_vars(StartDoorway(p))
        /\ WF_vars(ReadTicket(p))
        /\ WF_vars(AssignTicket(p))
        /\ WF_vars(TakeTicket(p))
        /\ WF_vars(CheckProcess(p))
        /\ WF_vars(EnterCS(p))
        /\ WF_vars(ExitCS(p))

\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Mutual Exclusion - at most one process in critical section
MutualExclusion ==
    \A p, q \in Procs: (p /= q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Alternative formulation of mutual exclusion
AtMostOneInCS ==
    Cardinality({p \in Procs: pc[p] = "cs"}) <= 1

\* State constraint for model checking
StateConstraint ==
    \A p \in Procs: ticket[p] <= MaxTicket

\* Liveness: every process that wants to enter CS eventually does
\* (starvation freedom)
Liveness ==
    \A p \in Procs: (pc[p] = "doorway") ~> (pc[p] = "cs")

\* Every process can always eventually enter CS if it tries
NoStarvation ==
    \A p \in Procs: (pc[p] /= "idle") ~> (pc[p] = "cs")

\* Deadlock freedom: if any process is trying, some process can progress
DeadlockFreedom ==
    (\E p \in Procs: pc[p] /= "idle" /\ pc[p] /= "cs") ~> 
    (\E p \in Procs: pc[p] = "cs")

========================================================================