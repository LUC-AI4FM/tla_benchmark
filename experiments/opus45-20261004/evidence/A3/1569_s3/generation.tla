---------------------------- MODULE BakeryAlgorithm ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

VARIABLES num, flag, pc, localMax, readSet, nextProc

vars == <<num, flag, pc, localMax, readSet, nextProc>>

Max(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : x >= y

\* Process comparison: (a, i) << (b, j) means process i has priority over j
\* when i has ticket a and j has ticket b
\* Returns TRUE if (a, i) < (b, j) in lexicographic order
Before(a, i, b, j) == (a < b) \/ (a = b /\ i < j)

TypeOK ==
    /\ num \in [Procs -> Nat]
    /\ flag \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> {"idle", "choose", "readOthers", "setTicket", 
                         "checkOthers", "waitFlag", "waitTurn", "cs", "exit"}]
    /\ localMax \in [Procs -> Nat]
    /\ readSet \in [Procs -> SUBSET Procs]
    /\ nextProc \in [Procs -> Procs]

Init ==
    /\ num = [p \in Procs |-> 0]
    /\ flag = [p \in Procs |-> FALSE]
    /\ pc = [p \in Procs |-> "idle"]
    /\ localMax = [p \in Procs |-> 0]
    /\ readSet = [p \in Procs |-> {}]
    /\ nextProc = [p \in Procs |-> 1]

\* Process p wants to enter the critical section
StartChoosing(p) ==
    /\ pc[p] = "idle"
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ localMax' = [localMax EXCEPT ![p] = 0]
    /\ readSet' = [readSet EXCEPT ![p] = {}]
    /\ pc' = [pc EXCEPT ![p] = "readOthers"]
    /\ UNCHANGED <<num, nextProc>>

\* Process p reads ticket numbers from other processes to compute max
ReadOthers(p) ==
    /\ pc[p] = "readOthers"
    /\ IF readSet[p] = Procs
       THEN /\ pc' = [pc EXCEPT ![p] = "setTicket"]
            /\ UNCHANGED <<num, flag, localMax, readSet, nextProc>>
       ELSE LET q == CHOOSE q \in Procs : q \notin readSet[p]
            IN /\ localMax' = [localMax EXCEPT ![p] = IF num[q] > localMax[p] 
                                                       THEN num[q] 
                                                       ELSE localMax[p]]
               /\ readSet' = [readSet EXCEPT ![p] = readSet[p] \cup {q}]
               /\ UNCHANGED <<num, flag, pc, nextProc>>

\* Process p sets its ticket number
SetTicket(p) ==
    /\ pc[p] = "setTicket"
    /\ num' = [num EXCEPT ![p] = localMax[p] + 1]
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ nextProc' = [nextProc EXCEPT ![p] = 1]
    /\ pc' = [pc EXCEPT ![p] = "checkOthers"]
    /\ UNCHANGED <<localMax, readSet>>

\* Process p checks other processes before entering CS
CheckOthers(p) ==
    /\ pc[p] = "checkOthers"
    /\ IF nextProc[p] > N
       THEN /\ pc' = [pc EXCEPT ![p] = "cs"]
            /\ UNCHANGED <<num, flag, localMax, readSet, nextProc>>
       ELSE IF nextProc[p] = p
            THEN /\ nextProc' = [nextProc EXCEPT ![p] = nextProc[p] + 1]
                 /\ UNCHANGED <<num, flag, pc, localMax, readSet>>
            ELSE /\ pc' = [pc EXCEPT ![p] = "waitFlag"]
                 /\ UNCHANGED <<num, flag, localMax, readSet, nextProc>>

\* Process p waits for process nextProc[p] to finish choosing
WaitFlag(p) ==
    /\ pc[p] = "waitFlag"
    /\ ~flag[nextProc[p]]
    /\ pc' = [pc EXCEPT ![p] = "waitTurn"]
    /\ UNCHANGED <<num, flag, localMax, readSet, nextProc>>

\* Process p waits for its turn (comparing tickets)
WaitTurn(p) ==
    /\ pc[p] = "waitTurn"
    /\ LET j == nextProc[p]
       IN \/ num[j] = 0
          \/ Before(num[p], p, num[j], j)
    /\ nextProc' = [nextProc EXCEPT ![p] = nextProc[p] + 1]
    /\ pc' = [pc EXCEPT ![p] = "checkOthers"]
    /\ UNCHANGED <<num, flag, localMax, readSet>>

\* Process p is in the critical section
InCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<num, flag, localMax, readSet, nextProc>>

\* Process p exits the critical section
Exit(p) ==
    /\ pc[p] = "exit"
    /\ num' = [num EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<flag, localMax, readSet, nextProc>>

\* Next state relation
Next ==
    \E p \in Procs :
        \/ StartChoosing(p)
        \/ ReadOthers(p)
        \/ SetTicket(p)
        \/ CheckOthers(p)
        \/ WaitFlag(p)
        \/ WaitTurn(p)
        \/ InCS(p)
        \/ Exit(p)

\* Fairness: weak fairness for all actions of each process
Fairness ==
    \A p \in Procs :
        /\ WF_vars(StartChoosing(p))
        /\ WF_vars(ReadOthers(p))
        /\ WF_vars(SetTicket(p))
        /\ WF_vars(CheckOthers(p))
        /\ WF_vars(WaitFlag(p))
        /\ WF_vars(WaitTurn(p))
        /\ WF_vars(InCS(p))
        /\ WF_vars(Exit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------
\* SAFETY INVARIANTS
--------------------------------------------------------------------------------

\* Mutual exclusion: at most one process in the critical section
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Alternative formulation
AtMostOneInCS ==
    Cardinality({p \in Procs : pc[p] = "cs"}) <= 1

--------------------------------------------------------------------------------
\* LIVENESS PROPERTIES
--------------------------------------------------------------------------------

\* Starvation freedom: if a process wants to enter CS, it eventually does
StarvationFreedom ==
    \A p \in Procs : (pc[p] = "choose") ~> (pc[p] = "cs")

\* Deadlock freedom: if some process is trying, some process eventually enters
DeadlockFreedom ==
    (\E p \in Procs : pc[p] \in {"choose", "readOthers", "setTicket", 
                                  "checkOthers", "waitFlag", "waitTurn"})
    ~> (\E q \in Procs : pc[q] = "cs")

--------------------------------------------------------------------------------
\* STATE CONSTRAINT FOR TLC MODEL CHECKING
--------------------------------------------------------------------------------

\* Bound ticket values to make state space finite for model checking
MaxTicketValue == 10

StateConstraint ==
    \A p \in Procs : num[p] <= MaxTicketValue /\ localMax[p] <= MaxTicketValue

================================================================================