---------------------------- MODULE Bakery ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS 
    N,          \* Number of processes
    MaxTicket   \* Maximum ticket value for finite-state model checking

ASSUME N \in Nat /\ N > 0
ASSUME MaxTicket \in Nat /\ MaxTicket > 0

Procs == 1..N

VARIABLES
    pc,         \* Program counter for each process
    choosing,   \* choosing[i] = TRUE if process i is choosing a number
    number      \* number[i] = ticket number of process i (0 means not in line)

vars == <<pc, choosing, number>>

TypeOK ==
    /\ pc \in [Procs -> {"idle", "choosing", "waiting", "cs"}]
    /\ choosing \in [Procs -> BOOLEAN]
    /\ number \in [Procs -> 0..MaxTicket]

\* Priority comparison: process i has priority over j if:
\* - j has number 0 (not competing), or
\* - i's number is smaller, or
\* - numbers are equal and i's ID is smaller
HasPriority(i, j) ==
    \/ number[j] = 0
    \/ number[i] < number[j]
    \/ (number[i] = number[j] /\ i < j)

\* Check if process i can enter CS (has priority over all other processes)
CanEnterCS(i) ==
    \A j \in Procs \ {i}:
        /\ ~choosing[j]
        /\ HasPriority(i, j)

\* Initial state: all processes idle, not choosing, with ticket 0
Init ==
    /\ pc = [i \in Procs |-> "idle"]
    /\ choosing = [i \in Procs |-> FALSE]
    /\ number = [i \in Procs |-> 0]

\* Process i starts trying to enter CS by beginning to choose a number
StartChoosing(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "choosing"]
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED number

\* Process i finishes choosing: picks max + 1 (bounded), clears choosing flag
FinishChoosing(i) ==
    /\ pc[i] = "choosing"
    /\ choosing[i] = TRUE
    /\ LET maxNum == IF Procs = {} THEN 0 
                     ELSE LET nums == {number[j] : j \in Procs}
                          IN CHOOSE m \in nums : \A n \in nums : m >= n
           newNum == IF maxNum + 1 > MaxTicket THEN MaxTicket ELSE maxNum + 1
       IN number' = [number EXCEPT ![i] = newNum]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "waiting"]

\* Process i enters the critical section when it has priority over everyone
EnterCS(i) ==
    /\ pc[i] = "waiting"
    /\ CanEnterCS(i)
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<choosing, number>>

\* Process i exits the critical section
ExitCS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ number' = [number EXCEPT ![i] = 0]
    /\ UNCHANGED choosing

\* Next state relation: some process takes a step
Next ==
    \E i \in Procs:
        \/ StartChoosing(i)
        \/ FinishChoosing(i)
        \/ EnterCS(i)
        \/ ExitCS(i)

\* Fairness: every process that can make progress eventually does
Fairness ==
    \A i \in Procs:
        /\ WF_vars(StartChoosing(i))
        /\ WF_vars(FinishChoosing(i))
        /\ WF_vars(EnterCS(i))
        /\ WF_vars(ExitCS(i))

\* Complete specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Mutual exclusion - at most one process in CS at any time
MutualExclusion ==
    \A i, j \in Procs: (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Alternative formulation: cardinality of processes in CS is at most 1
MutualExclusionAlt ==
    Cardinality({i \in Procs : pc[i] = "cs"}) <= 1

\* Liveness: Every process trying to enter CS eventually does
Liveness ==
    \A i \in Procs: (pc[i] = "waiting") ~> (pc[i] = "cs")

\* Liveness: No starvation - if a process starts choosing, it eventually enters CS
NoStarvation ==
    \A i \in Procs: (pc[i] = "choosing") ~> (pc[i] = "cs")

=======================================================================