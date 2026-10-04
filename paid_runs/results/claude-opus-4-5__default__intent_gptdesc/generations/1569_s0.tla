-------------------------------- MODULE Bakery --------------------------------
\* Lamport's Bakery Algorithm for N concurrent processes
\* Formal specification for model checking with TLC

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    N,              \* Number of processes (processes are 1..N)
    MaxTicket       \* Bound on ticket values for model checking

ASSUME N \in Nat /\ N > 0
ASSUME MaxTicket \in Nat /\ MaxTicket >= N

VARIABLES
    pc,         \* Program counter for each process
    choosing,   \* choosing[i] = TRUE when process i is selecting a ticket
    ticket,     \* ticket[i] = ticket number held by process i (0 means not in protocol)
    reading     \* reading[i] = which process i is currently checking in the wait loop

\* Process identifiers
Procs == 1..N

\* Program counter states
PCStates == {"idle", "choosing", "waiting", "cs", "exit"}

\* Type invariant for state space
TypeOK ==
    /\ pc \in [Procs -> PCStates]
    /\ choosing \in [Procs -> BOOLEAN]
    /\ ticket \in [Procs -> 0..MaxTicket]
    /\ reading \in [Procs -> 0..N]

--------------------------------------------------------------------------------
\* Initial state: all processes idle, no tickets, not choosing
--------------------------------------------------------------------------------

Init ==
    /\ pc = [i \in Procs |-> "idle"]
    /\ choosing = [i \in Procs |-> FALSE]
    /\ ticket = [i \in Procs |-> 0]
    /\ reading = [i \in Procs |-> 0]

--------------------------------------------------------------------------------
\* Helper: compute maximum ticket currently held
--------------------------------------------------------------------------------

MaxCurrentTicket == 
    IF \E i \in Procs : ticket[i] > 0
    THEN LET S == {ticket[i] : i \in Procs}
         IN CHOOSE m \in S : \A x \in S : m >= x
    ELSE 0

\* Ticket comparison with process id tie-breaker
\* Returns TRUE if (ticket_a, a) << (ticket_b, b) in lexicographic order
\* where 0 means "not competing" (so ticket 0 never has priority)
Precedes(ticket_a, a, ticket_b, b) ==
    /\ ticket_a > 0
    /\ \/ ticket_b = 0
       \/ ticket_a < ticket_b
       \/ (ticket_a = ticket_b /\ a < b)

--------------------------------------------------------------------------------
\* Process Actions
--------------------------------------------------------------------------------

\* Process i starts the protocol by entering the choosing phase
StartChoosing(i) ==
    /\ pc[i] = "idle"
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "choosing"]
    /\ UNCHANGED <<ticket, reading>>

\* Process i finishes choosing: takes a ticket number
FinishChoosing(i) ==
    /\ pc[i] = "choosing"
    /\ LET newTicket == MaxCurrentTicket + 1
       IN /\ newTicket <= MaxTicket  \* Bounded model checking constraint
          /\ ticket' = [ticket EXCEPT ![i] = newTicket]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ reading' = [reading EXCEPT ![i] = 1]  \* Start checking from process 1
    /\ pc' = [pc EXCEPT ![i] = "waiting"]

\* Process i is waiting and checking process reading[i]
\* Case 1: reading[i] is self - skip to next
CheckSelf(i) ==
    /\ pc[i] = "waiting"
    /\ reading[i] = i
    /\ reading' = [reading EXCEPT ![i] = reading[i] + 1]
    /\ UNCHANGED <<pc, choosing, ticket>>

\* Case 2: reading[i] is choosing - must wait (re-read, modeled as no progress)
WaitForChoosing(i) ==
    /\ pc[i] = "waiting"
    /\ reading[i] \in Procs
    /\ reading[i] # i
    /\ choosing[reading[i]] = TRUE
    /\ UNCHANGED <<pc, choosing, ticket, reading>>  \* Spin/wait

\* Case 3: reading[i] has smaller ticket (or same ticket with smaller id) - wait
WaitForTicket(i) ==
    /\ pc[i] = "waiting"
    /\ reading[i] \in Procs
    /\ reading[i] # i
    /\ choosing[reading[i]] = FALSE
    /\ Precedes(ticket[reading[i]], reading[i], ticket[i], i)
    /\ UNCHANGED <<pc, choosing, ticket, reading>>  \* Spin/wait

\* Case 4: reading[i] doesn't block us - advance to next process
AdvanceReading(i) ==
    /\ pc[i] = "waiting"
    /\ reading[i] \in Procs
    /\ reading[i] # i
    /\ choosing[reading[i]] = FALSE
    /\ ~Precedes(ticket[reading[i]], reading[i], ticket[i], i)
    /\ reading' = [reading EXCEPT ![i] = reading[i] + 1]
    /\ UNCHANGED <<pc, choosing, ticket>>

\* Case 5: finished checking all processes - enter CS
EnterCS(i) ==
    /\ pc[i] = "waiting"
    /\ reading[i] > N  \* Checked all processes
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<choosing, ticket, reading>>

\* Process i exits the critical section
ExitCS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED <<choosing, ticket, reading>>

\* Process i releases ticket and returns to idle
ReleaseTicket(i) ==
    /\ pc[i] = "exit"
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ reading' = [reading EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED <<choosing>>

--------------------------------------------------------------------------------
\* Next state relation
--------------------------------------------------------------------------------

ProcessAction(i) ==
    \/ StartChoosing(i)
    \/ FinishChoosing(i)
    \/ CheckSelf(i)
    \/ WaitForChoosing(i)
    \/ WaitForTicket(i)
    \/ AdvanceReading(i)
    \/ EnterCS(i)
    \/ ExitCS(i)
    \/ ReleaseTicket(i)

Next == \E i \in Procs : ProcessAction(i)

--------------------------------------------------------------------------------
\* Fairness conditions
--------------------------------------------------------------------------------

\* Weak fairness for each process's actions that make progress
\* This excludes the spinning/waiting actions
ProgressAction(i) ==
    \/ StartChoosing(i)
    \/ FinishChoosing(i)
    \/ CheckSelf(i)
    \/ AdvanceReading(i)
    \/ EnterCS(i)
    \/ ExitCS(i)
    \/ ReleaseTicket(i)

Fairness == \A i \in Procs : WF_<<pc, choosing, ticket, reading>>(ProgressAction(i))

--------------------------------------------------------------------------------
\* Complete specification
--------------------------------------------------------------------------------

Spec == Init /\ [][Next]_<<pc, choosing, ticket, reading>> /\ Fairness

--------------------------------------------------------------------------------
\* SAFETY INVARIANTS
--------------------------------------------------------------------------------

\* Mutual Exclusion: at most one process in CS
MutualExclusion ==
    \A i, j \in Procs : (pc[i] = "cs" /\ pc[j] = "cs") => i = j

\* Equivalent formulation: cardinality of processes in CS <= 1
MutualExclusionCard ==
    Cardinality({i \in Procs : pc[i] = "cs"}) <= 1

\* Ticket bound invariant: all tickets within bound
TicketBoundInvariant ==
    \A i \in Procs : ticket[i] <= MaxTicket

\* Choosing flag consistency: only set when pc is "choosing"
ChoosingConsistency ==
    \A i \in Procs : choosing[i] = TRUE => pc[i] = "choosing"

\* Ticket consistency: ticket > 0 only when actively in protocol
TicketConsistency ==
    \A i \in Procs : 
        (pc[i] = "idle" => ticket[i] = 0) /\
        (pc[i] \in {"waiting", "cs", "exit"} => ticket[i] > 0)

\* Reading variable consistency
ReadingConsistency ==
    \A i \in Procs :
        /\ (pc[i] = "waiting" => reading[i] \in 1..(N+1))
        /\ (pc[i] \in {"idle", "choosing", "cs", "exit"} => 
            (pc[i] = "idle" => reading[i] = 0))

\* Ordering invariant: if two processes are both past choosing with tickets,
\* and one is in CS, then it must have priority over all others trying to enter
OrderingInvariant ==
    \A i \in Procs :
        pc[i] = "cs" =>
            \A j \in Procs \ {i} :
                (ticket[j] > 0 /\ ~choosing[j]) =>
                    Precedes(ticket[i], i, ticket[j], j)

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeOK
    /\ MutualExclusion
    /\ TicketBoundInvariant
    /\ ChoosingConsistency
    /\ TicketConsistency
    /\ OrderingInvariant

--------------------------------------------------------------------------------
\* DEADLOCK FREEDOM
--------------------------------------------------------------------------------

\* A process can make progress (not stuck)
CanProgress(i) ==
    \/ pc[i] = "idle"                           \* Can start choosing
    \/ pc[i] = "choosing"                       \* Can finish choosing (if under bound)
    \/ pc[i] = "cs"                             \* Can exit CS
    \/ pc[i] = "exit"                           \* Can release ticket
    \/ (pc[i] = "waiting" /\ reading[i] > N)    \* Can enter CS
    \/ (pc[i] = "waiting" /\ reading[i] = i)    \* Can skip self
    \/ (pc[i] = "waiting" /\ reading[i] \in Procs /\ reading[i] # i /\
        choosing[reading[i]] = FALSE /\
        ~Precedes(ticket[reading[i]], reading[i], ticket[i], i))  \* Can advance

\* No deadlock: if any process is trying to enter, some process can make progress
\* A process is "trying" if it's in choosing or waiting state
Trying(i) == pc[i] \in {"choosing", "waiting"}

NoDeadlock ==
    (\E i \in Procs : Trying(i)) => (\E i \in Procs : CanProgress(i))

\* Stronger: the system can always make some transition
SystemCanProgress ==
    \E i \in Procs : 
        \/ pc[i] = "idle"
        \/ pc[i] = "choosing" /\ MaxCurrentTicket < MaxTicket
        \/ pc[i] = "cs"
        \/ pc[i] = "exit"
        \/ (pc[i] = "waiting" /\ 
            (reading[i] > N \/ reading[i] = i \/
             (reading[i] \in Procs /\ reading[i] # i /\
              ~choosing[reading[i]] /\
              ~Precedes(ticket[reading[i]], reading[i], ticket[i], i))))

--------------------------------------------------------------------------------
\* LIVENESS PROPERTIES
--------------------------------------------------------------------------------

\* Eventually enter CS: if a process starts trying, it eventually enters CS
\* Requires weak fairness on progress actions
EventuallyEnterCS(i) ==
    (pc[i] = "choosing") ~> (pc[i] = "cs")

\* Every process that tries eventually enters
AllEventuallyEnter ==
    \A i \in Procs : EventuallyEnterCS(i)

\* Eventually release: after entering CS, eventually return to idle
EventuallyRelease(i) ==
    (pc[i] = "cs") ~> (pc[i] = "idle")

\* Ticket eventually reset after leaving CS
TicketEventuallyReset(i) ==
    (pc[i] = "exit") ~> (ticket[i] = 0)

\* All tickets eventually reset
AllTicketsEventuallyReset ==
    \A i \in Procs : TicketEventuallyReset(i)

\* Starvation freedom: a trying process eventually gets served
StarvationFreedom ==
    \A i \in Procs : (Trying(i) ~> pc[i] = "cs")

--------------------------------------------------------------------------------
\* DEBUGGING / INSPECTION HELPERS
--------------------------------------------------------------------------------

\* Count of processes in each state
ProcessesIdle == Cardinality({i \in Procs : pc[i] = "idle"})
ProcessesChoosing == Cardinality({i \in Procs : pc[i] = "choosing"})
ProcessesWaiting == Cardinality({i \in Procs : pc[i] = "waiting"})
ProcessesInCS == Cardinality({i \in Procs : pc[i] = "cs"})
ProcessesExiting == Cardinality({i \in Procs : pc[i] = "exit"})

\* Current maximum ticket in use
CurrentMaxTicket == MaxCurrentTicket

\* Set of processes currently contending (have non-zero tickets)
ContendingProcesses == {i \in Procs : ticket[i] > 0}

\* Process with minimum ticket among contenders (should be in or entering CS)
MinTicketProcess ==
    IF ContendingProcesses = {} THEN 0
    ELSE CHOOSE i \in ContendingProcesses :
            \A j \in ContendingProcesses : 
                ticket[i] < ticket[j] \/ (ticket[i] = ticket[j] /\ i <= j)

================================================================================