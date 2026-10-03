---------------------------- MODULE BakeryAlgorithm ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS NumProcs

ASSUME NumProcs \in Nat /\ NumProcs > 0

Procs == 1..NumProcs

VARIABLES
    num,        \* num[p] is the ticket number of process p
    choosing,   \* choosing[p] is TRUE if process p is choosing a ticket
    localMax,   \* localMax[p] is the local maximum computed by process p
    readSet,    \* readSet[p] is the set of processes whose tickets p has read
    nxt,        \* nxt[p] is the next process that p will examine in doorway/waiting
    pc          \* pc[p] is the control location of process p

vars == <<num, choosing, localMax, readSet, nxt, pc>>

\* Control locations for each process:
\* "idle"     - not trying to enter critical section
\* "choose1"  - starting to choose, reading tickets
\* "choose2"  - computing max and setting ticket
\* "wait1"    - waiting for other processes (checking choosing flag)
\* "wait2"    - waiting for other processes (checking ticket priority)
\* "cs"       - in critical section
\* "exit"     - exiting critical section

TypeOK ==
    /\ num \in [Procs -> Nat]
    /\ choosing \in [Procs -> BOOLEAN]
    /\ localMax \in [Procs -> Nat]
    /\ readSet \in [Procs -> SUBSET Procs]
    /\ nxt \in [Procs -> Procs]
    /\ pc \in [Procs -> {"idle", "choose1", "choose2", "wait1", "wait2", "cs", "exit"}]

Init ==
    /\ num = [p \in Procs |-> 0]
    /\ choosing = [p \in Procs |-> FALSE]
    /\ localMax = [p \in Procs |-> 0]
    /\ readSet = [p \in Procs |-> {}]
    /\ nxt = [p \in Procs |-> 1]
    /\ pc = [p \in Procs |-> "idle"]

\* Process p starts trying to enter critical section
StartChoosing(p) ==
    /\ pc[p] = "idle"
    /\ choosing' = [choosing EXCEPT ![p] = TRUE]
    /\ readSet' = [readSet EXCEPT ![p] = {}]
    /\ localMax' = [localMax EXCEPT ![p] = 0]
    /\ nxt' = [nxt EXCEPT ![p] = 1]
    /\ pc' = [pc EXCEPT ![p] = "choose1"]
    /\ UNCHANGED num

\* Process p reads tickets to compute maximum
ReadTickets(p) ==
    /\ pc[p] = "choose1"
    /\ IF nxt[p] <= NumProcs
       THEN /\ localMax' = [localMax EXCEPT ![p] = IF num[nxt[p]] > localMax[p] 
                                                   THEN num[nxt[p]] 
                                                   ELSE localMax[p]]
            /\ readSet' = [readSet EXCEPT ![p] = readSet[p] \cup {nxt[p]}]
            /\ nxt' = [nxt EXCEPT ![p] = nxt[p] + 1]
            /\ pc' = [pc EXCEPT ![p] = "choose1"]
            /\ UNCHANGED <<num, choosing>>
       ELSE /\ pc' = [pc EXCEPT ![p] = "choose2"]
            /\ UNCHANGED <<num, choosing, localMax, readSet, nxt>>

\* Process p sets its ticket number and finishes choosing
SetTicket(p) ==
    /\ pc[p] = "choose2"
    /\ num' = [num EXCEPT ![p] = localMax[p] + 1]
    /\ choosing' = [choosing EXCEPT ![p] = FALSE]
    /\ nxt' = [nxt EXCEPT ![p] = 1]
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<localMax, readSet>>

\* Process p waits for process nxt[p] to stop choosing
WaitForChoosing(p) ==
    /\ pc[p] = "wait1"
    /\ IF nxt[p] <= NumProcs
       THEN IF choosing[nxt[p]]
            THEN UNCHANGED vars  \* Busy wait
            ELSE /\ pc' = [pc EXCEPT ![p] = "wait2"]
                 /\ UNCHANGED <<num, choosing, localMax, readSet, nxt>>
       ELSE /\ pc' = [pc EXCEPT ![p] = "cs"]
            /\ UNCHANGED <<num, choosing, localMax, readSet, nxt>>

\* Lexicographic comparison: (a, i) << (b, j)
LessThan(a, i, b, j) ==
    \/ a < b
    \/ (a = b /\ i < j)

\* Process p checks if it has priority over process nxt[p]
CheckPriority(p) ==
    /\ pc[p] = "wait2"
    /\ nxt[p] <= NumProcs
    /\ LET other == nxt[p]
           otherNum == num[other]
       IN IF otherNum = 0 \/ LessThan(num[p], p, otherNum, other)
          THEN /\ nxt' = [nxt EXCEPT ![p] = nxt[p] + 1]
               /\ pc' = [pc EXCEPT ![p] = "wait1"]
               /\ UNCHANGED <<num, choosing, localMax, readSet>>
          ELSE UNCHANGED vars  \* Busy wait

\* Process p enters critical section
EnterCS(p) ==
    /\ pc[p] = "wait1"
    /\ nxt[p] > NumProcs
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED <<num, choosing, localMax, readSet, nxt>>

\* Process p exits critical section
ExitCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<num, choosing, localMax, readSet, nxt>>

\* Process p resets its ticket and returns to idle
Reset(p) ==
    /\ pc[p] = "exit"
    /\ num' = [num EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<choosing, localMax, readSet, nxt>>

\* Next state relation for a single process
ProcNext(p) ==
    \/ StartChoosing(p)
    \/ ReadTickets(p)
    \/ SetTicket(p)
    \/ WaitForChoosing(p)
    \/ CheckPriority(p)
    \/ EnterCS(p)
    \/ ExitCS(p)
    \/ Reset(p)

Next == \E p \in Procs : ProcNext(p)

\* Fairness: weak fairness for each process action
Fairness == \A p \in Procs : WF_vars(ProcNext(p))

Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------
\* Safety Invariant: Mutual Exclusion
\* At most one process can be in the critical section at a time

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Alternative formulation
MutualExclusionAlt ==
    Cardinality({p \in Procs : pc[p] = "cs"}) <= 1

--------------------------------------------------------------------------------
\* State constraint for TLC model checking to bound ticket values

MaxTicketValue == 10

StateConstraint ==
    \A p \in Procs : num[p] <= MaxTicketValue

--------------------------------------------------------------------------------
\* Liveness Properties

\* Deadlock freedom: if some process wants to enter CS, eventually some process enters
DeadlockFreedom ==
    (\E p \in Procs : pc[p] \in {"choose1", "choose2", "wait1", "wait2"}) 
    ~> (\E p \in Procs : pc[p] = "cs")

\* Starvation freedom: every process that wants to enter CS eventually does
StarvationFreedom ==
    \A p \in Procs : (pc[p] = "choose1") ~> (pc[p] = "cs")

\* Every process in CS eventually exits
EventualExit ==
    \A p \in Procs : (pc[p] = "cs") ~> (pc[p] = "idle")

================================================================================