-------------------------- MODULE BakeryAlgorithm --------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT NumProcs, MaxNum

ASSUME NumProcs \in Nat /\ NumProcs > 0
ASSUME MaxNum \in Nat /\ MaxNum > 0

Procs == 1..NumProcs

VARIABLES num, choosing, localMax, localRead, nxt, pc

vars == <<num, choosing, localMax, localRead, nxt, pc>>

TypeOK ==
    /\ num \in [Procs -> Nat]
    /\ choosing \in [Procs -> BOOLEAN]
    /\ localMax \in [Procs -> Nat]
    /\ localRead \in [Procs -> SUBSET Procs]
    /\ nxt \in [Procs -> Procs]
    /\ pc \in [Procs -> {"ncs", "start", "readMax", "setNum", "wait", "checkChoosing", "checkNum", "cs", "exit"}]

Init ==
    /\ num = [p \in Procs |-> 0]
    /\ choosing = [p \in Procs |-> FALSE]
    /\ localMax = [p \in Procs |-> 0]
    /\ localRead = [p \in Procs |-> {}]
    /\ nxt = [p \in Procs |-> 1]
    /\ pc = [p \in Procs |-> "ncs"]

\* Non-critical section - move to start
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<num, choosing, localMax, localRead, nxt>>

\* Start choosing - set choosing flag and prepare to read max
start(self) ==
    /\ pc[self] = "start"
    /\ choosing' = [choosing EXCEPT ![self] = TRUE]
    /\ localMax' = [localMax EXCEPT ![self] = 0]
    /\ localRead' = [localRead EXCEPT ![self] = {}]
    /\ pc' = [pc EXCEPT ![self] = "readMax"]
    /\ UNCHANGED <<num, nxt>>

\* Read maximum ticket number from other processes
readMax(self) ==
    /\ pc[self] = "readMax"
    /\ IF localRead[self] # Procs
       THEN LET p == CHOOSE q \in Procs : q \notin localRead[self]
            IN /\ localMax' = [localMax EXCEPT ![self] = IF num[p] > localMax[self] THEN num[p] ELSE localMax[self]]
               /\ localRead' = [localRead EXCEPT ![self] = localRead[self] \cup {p}]
               /\ pc' = [pc EXCEPT ![self] = "readMax"]
               /\ UNCHANGED <<num, choosing, nxt>>
       ELSE /\ pc' = [pc EXCEPT ![self] = "setNum"]
            /\ UNCHANGED <<num, choosing, localMax, localRead, nxt>>

\* Set own ticket number
setNum(self) ==
    /\ pc[self] = "setNum"
    /\ num' = [num EXCEPT ![self] = localMax[self] + 1]
    /\ choosing' = [choosing EXCEPT ![self] = FALSE]
    /\ nxt' = [nxt EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "wait"]
    /\ UNCHANGED <<localMax, localRead>>

\* Wait loop - check each process
wait(self) ==
    /\ pc[self] = "wait"
    /\ IF nxt[self] > NumProcs
       THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED <<num, choosing, localMax, localRead, nxt>>
       ELSE /\ pc' = [pc EXCEPT ![self] = "checkChoosing"]
            /\ UNCHANGED <<num, choosing, localMax, localRead, nxt>>

\* Wait for process nxt[self] to finish choosing
checkChoosing(self) ==
    /\ pc[self] = "checkChoosing"
    /\ ~choosing[nxt[self]]
    /\ pc' = [pc EXCEPT ![self] = "checkNum"]
    /\ UNCHANGED <<num, choosing, localMax, localRead, nxt>>

\* Check ticket number comparison
checkNum(self) ==
    /\ pc[self] = "checkNum"
    /\ LET other == nxt[self]
       IN \/ num[other] = 0
          \/ num[self] < num[other]
          \/ (num[self] = num[other] /\ self < other)
    /\ nxt' = [nxt EXCEPT ![self] = nxt[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "wait"]
    /\ UNCHANGED <<num, choosing, localMax, localRead>>

\* Critical section
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<num, choosing, localMax, localRead, nxt>>

\* Exit critical section
exit(self) ==
    /\ pc[self] = "exit"
    /\ num' = [num EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<choosing, localMax, localRead, nxt>>

\* Combined next state for a single process
Step(self) ==
    \/ ncs(self)
    \/ start(self)
    \/ readMax(self)
    \/ setNum(self)
    \/ wait(self)
    \/ checkChoosing(self)
    \/ checkNum(self)
    \/ cs(self)
    \/ exit(self)

Next == \E self \in Procs : Step(self)

\* State constraint for bounded model checking
StateConstraint == \A p \in Procs : num[p] <= MaxNum

\* Mutual exclusion invariant: at most one process in CS
MutualExclusion == \A p, q \in Procs : (pc[p] = "cs" /\ pc[q] = "cs") => p = q

Invariant == MutualExclusion

Spec == Init /\ [][Next]_vars

=============================================================================