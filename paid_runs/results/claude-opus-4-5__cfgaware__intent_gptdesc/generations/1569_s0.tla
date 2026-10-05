---------------------------- MODULE Bakery ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumProcs, MaxNum

ASSUME NumProcs \in Nat /\ NumProcs > 0
ASSUME MaxNum \in Nat /\ MaxNum > 0

Procs == 1..NumProcs

VARIABLES
    pc,         \* Program counter for each process
    num,        \* Ticket number for each process (0 means not in protocol)
    choosing,   \* Flag indicating process is choosing a ticket
    j           \* Index variable for scanning other processes

vars == <<pc, num, choosing, j>>

\* Program counter states
\* "idle"     - not trying to enter critical section
\* "choose"   - about to choose a ticket number
\* "scan"     - scanning other processes' numbers to find max
\* "wait"     - waiting for turn (checking other processes)
\* "check"    - checking a specific process j
\* "cs"       - in critical section
\* "exit"     - leaving critical section

TypeOK ==
    /\ pc \in [Procs -> {"idle", "choose", "scan", "wait", "check", "cs", "exit"}]
    /\ num \in [Procs -> 0..MaxNum]
    /\ choosing \in [Procs -> BOOLEAN]
    /\ j \in [Procs -> 0..NumProcs]

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ num = [p \in Procs |-> 0]
    /\ choosing = [p \in Procs |-> FALSE]
    /\ j = [p \in Procs |-> 0]

\* Helper: Maximum ticket number currently held by any process
MaxTicket == 
    LET S == {num[p] : p \in Procs}
    IN IF S = {} THEN 0 ELSE CHOOSE m \in S : \A x \in S : x <= m

\* Ticket comparison: (a, i) << (b, k) means process i with ticket a has priority
\* Returns TRUE if (num_i, i) < (num_k, k) in lexicographic order
HasPriority(i, k) ==
    \/ num[i] < num[k]
    \/ (num[i] = num[k] /\ i < k)

\* Process p starts trying to enter critical section
StartChoosing(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "choose"]
    /\ choosing' = [choosing EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<num, j>>

\* Process p computes its ticket number (scan for max + 1)
ChooseTicket(p) ==
    /\ pc[p] = "choose"
    /\ LET newNum == (MaxTicket + 1)
       IN IF newNum <= MaxNum
          THEN /\ num' = [num EXCEPT ![p] = newNum]
               /\ pc' = [pc EXCEPT ![p] = "scan"]
          ELSE /\ UNCHANGED <<num, pc>>  \* Block if would exceed MaxNum
    /\ UNCHANGED <<choosing, j>>

\* Process p finishes choosing and starts waiting phase
FinishChoosing(p) ==
    /\ pc[p] = "scan"
    /\ choosing' = [choosing EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ j' = [j EXCEPT ![p] = 1]
    /\ UNCHANGED <<num>>

\* Process p initializes check of process j[p]
StartWait(p) ==
    /\ pc[p] = "wait"
    /\ j[p] <= NumProcs
    /\ pc' = [pc EXCEPT ![p] = "check"]
    /\ UNCHANGED <<num, choosing, j>>

\* Process p has checked all processes, enters CS
EnterCS(p) ==
    /\ pc[p] = "wait"
    /\ j[p] > NumProcs
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED <<num, choosing, j>>

\* Process p checks process j[p]
\* Must wait if j[p] is choosing or has priority
CheckProcess(p) ==
    /\ pc[p] = "check"
    /\ LET k == j[p]
       IN /\ ~choosing[k]  \* Wait until k is not choosing
          /\ \/ num[k] = 0  \* k is not competing
             \/ HasPriority(p, k)  \* p has priority over k
    /\ j' = [j EXCEPT ![p] = j[p] + 1]
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED <<num, choosing>>

\* Process p is in critical section and can stay or leave
InCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<num, choosing, j>>

\* Process p exits critical section
ExitCS(p) ==
    /\ pc[p] = "exit"
    /\ num' = [num EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<choosing, j>>

\* A process action
Process(p) ==
    \/ StartChoosing(p)
    \/ ChooseTicket(p)
    \/ FinishChoosing(p)
    \/ StartWait(p)
    \/ EnterCS(p)
    \/ CheckProcess(p)
    \/ InCS(p)
    \/ ExitCS(p)

Next == \E p \in Procs : Process(p)

\* Fairness: weak fairness for each process action
Fairness == \A p \in Procs : WF_vars(Process(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* ----- SAFETY PROPERTIES -----

\* Mutual Exclusion: at most one process in critical section
MutualExclusion ==
    \A p, q \in Procs : (pc[p] = "cs" /\ pc[q] = "cs") => p = q

\* Alternative formulation
AtMostOneInCS ==
    Cardinality({p \in Procs : pc[p] = "cs"}) <= 1

\* Ticket values within bound
TicketBound ==
    \A p \in Procs : num[p] <= MaxNum

\* Ticket ordering property: if two processes are past choosing with non-zero tickets,
\* their tickets define a total order (with process id as tiebreaker)
TicketOrderingWellDefined ==
    \A p, q \in Procs :
        (p # q /\ num[p] > 0 /\ num[q] > 0 /\ ~choosing[p] /\ ~choosing[q]) =>
        (HasPriority(p, q) \/ HasPriority(q, p))

\* If a process is in CS, no other competing process has priority
CSHasPriority ==
    \A p \in Procs :
        pc[p] = "cs" =>
        \A q \in Procs \ {p} :
            (num[q] > 0 /\ ~choosing[q]) => HasPriority(p, q)

\* Choosing flag consistency
ChoosingConsistency ==
    \A p \in Procs :
        choosing[p] => (pc[p] = "choose" \/ pc[p] = "scan")

\* If process is idle, its ticket should be 0
IdleHasZeroTicket ==
    \A p \in Procs : pc[p] = "idle" => num[p] = 0

\* Combined invariant for model checking
Invariant ==
    /\ TypeOK
    /\ MutualExclusion
    /\ TicketBound
    /\ TicketOrderingWellDefined
    /\ CSHasPriority
    /\ ChoosingConsistency

\* ----- LIVENESS PROPERTIES -----

\* Every process that starts trying eventually enters CS
\* (requires weak fairness on process actions)
Liveness ==
    \A p \in Procs : (pc[p] = "choose") ~> (pc[p] = "cs")

\* Every process in CS eventually exits
EventualExit ==
    \A p \in Procs : (pc[p] = "cs") ~> (pc[p] = "idle")

\* Process eventually resets ticket after leaving CS
EventualReset ==
    \A p \in Procs : (pc[p] = "exit") ~> (num[p] = 0)

\* ----- DEADLOCK FREEDOM -----

\* At least one process can make progress if any is trying
\* (This is implied by the algorithm but we state it explicitly)
SomeoneCanProgress ==
    (\E p \in Procs : pc[p] # "idle") =>
    (\E p \in Procs : ENABLED(Process(p)))

\* No deadlock: always some action is enabled
NoDeadlock ==
    ENABLED(Next)

\* ----- AUXILIARY PREDICATES FOR INSPECTION -----

\* Number of processes currently choosing
NumChoosing == Cardinality({p \in Procs : choosing[p]})

\* Number of processes with non-zero tickets (competing)
NumCompeting == Cardinality({p \in Procs : num[p] > 0})

\* Number of processes in waiting phase
NumWaiting == Cardinality({p \in Procs : pc[p] \in {"wait", "check"}})

\* Current maximum ticket in use
CurrentMaxTicket == MaxTicket

\* Processes currently in critical section
ProcessesInCS == {p \in Procs : pc[p] = "cs"}

=======================================================================