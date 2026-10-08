---------------------------- MODULE BakeryMutex ----------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumProcs, MaxNum

ASSUME NumProcs \in Nat /\ NumProcs > 0
ASSUME MaxNum \in Nat /\ MaxNum > 0

Procs == 1..NumProcs

VARIABLES pc, num, choosing, readSet, maxRead

vars == <<pc, num, choosing, readSet, maxRead>>

TypeOK ==
    /\ pc \in [Procs -> {"idle", "choose_start", "read_others", "choose_end", 
                         "wait_start", "wait_check", "cs", "exit"}]
    /\ num \in [Procs -> 0..MaxNum]
    /\ choosing \in [Procs -> BOOLEAN]
    /\ readSet \in [Procs -> SUBSET Procs]
    /\ maxRead \in [Procs -> 0..MaxNum]

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ num = [p \in Procs |-> 0]
    /\ choosing = [p \in Procs |-> FALSE]
    /\ readSet = [p \in Procs |-> {}]
    /\ maxRead = [p \in Procs |-> 0]

\* Process p starts trying to enter critical section
StartChoosing(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "choose_start"]
    /\ choosing' = [choosing EXCEPT ![p] = TRUE]
    /\ readSet' = [readSet EXCEPT ![p] = Procs \ {p}]
    /\ maxRead' = [maxRead EXCEPT ![p] = 0]
    /\ UNCHANGED num

\* Process p reads another process q's ticket number during choosing phase
ReadOther(p) ==
    /\ pc[p] = "choose_start"
    /\ readSet[p] /= {}
    /\ \E q \in readSet[p]:
        /\ ~choosing[q]  \* Wait until q is not choosing
        /\ readSet' = [readSet EXCEPT ![p] = readSet[p] \ {q}]
        /\ maxRead' = [maxRead EXCEPT ![p] = IF num[q] > maxRead[p] THEN num[q] ELSE maxRead[p]]
        /\ UNCHANGED <<pc, num, choosing>>

\* Process p finishes reading and assigns ticket
FinishChoosing(p) ==
    /\ pc[p] = "choose_start"
    /\ readSet[p] = {}
    /\ num' = [num EXCEPT ![p] = maxRead[p] + 1]
    /\ choosing' = [choosing EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "wait_start"]
    /\ readSet' = [readSet EXCEPT ![p] = Procs \ {p}]
    /\ UNCHANGED maxRead

\* Process p starts waiting phase - check another process
WaitCheck(p) ==
    /\ pc[p] = "wait_start"
    /\ readSet[p] /= {}
    /\ \E q \in readSet[p]:
        /\ ~choosing[q]  \* First wait until q is not choosing
        /\ \/ num[q] = 0  \* q is not competing
           \/ num[p] < num[q]  \* p has lower ticket
           \/ (num[p] = num[q] /\ p < q)  \* Same ticket, lower ID wins
        /\ readSet' = [readSet EXCEPT ![p] = readSet[p] \ {q}]
        /\ UNCHANGED <<pc, num, choosing, maxRead>>

\* Process p has checked all others and can enter critical section
EnterCS(p) ==
    /\ pc[p] = "wait_start"
    /\ readSet[p] = {}
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED <<num, choosing, readSet, maxRead>>

\* Process p exits critical section
ExitCS(p) ==
    /\ pc[p] = "cs"
    /\ num' = [num EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<choosing, readSet, maxRead>>

Next ==
    \E p \in Procs:
        \/ StartChoosing(p)
        \/ ReadOther(p)
        \/ FinishChoosing(p)
        \/ WaitCheck(p)
        \/ EnterCS(p)
        \/ ExitCS(p)

\* State constraint for bounded model checking
StateConstraint == \A p \in Procs: num[p] <= MaxNum

\* Mutual exclusion: at most one process in critical section
MutualExclusion == \A p, q \in Procs: (p /= q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

Invariant == MutualExclusion

Spec == Init /\ [][Next]_vars

=============================================================================