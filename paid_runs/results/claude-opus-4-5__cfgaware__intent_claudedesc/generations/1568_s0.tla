---------------------------- MODULE Bakery ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT NumProcs, MaxTicket

ASSUME NumProcs \in Nat /\ NumProcs > 0
ASSUME MaxTicket \in Nat /\ MaxTicket > 0

Procs == 1..NumProcs

VARIABLES pc, num, choosing

vars == <<pc, num, choosing>>

TypeOK ==
    /\ pc \in [Procs -> {"idle", "choosing", "scanning", "waiting", "cs", "exit"}]
    /\ num \in [Procs -> 0..MaxTicket]
    /\ choosing \in [Procs -> BOOLEAN]

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ num = [p \in Procs |-> 0]
    /\ choosing = [p \in Procs |-> FALSE]

StartChoosing(p) ==
    /\ pc[p] = "idle"
    /\ choosing' = [choosing EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED num

ComputeTicket(p) ==
    /\ pc[p] = "choosing"
    /\ LET maxNum == IF Procs = {} THEN 0 
                     ELSE LET S == {num[q] : q \in Procs}
                          IN CHOOSE m \in S : \A n \in S : n <= m
           newNum == IF maxNum + 1 > MaxTicket THEN MaxTicket ELSE maxNum + 1
       IN num' = [num EXCEPT ![p] = newNum]
    /\ pc' = [pc EXCEPT ![p] = "scanning"]
    /\ UNCHANGED choosing

FinishChoosing(p) ==
    /\ pc[p] = "scanning"
    /\ choosing' = [choosing EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ UNCHANGED num

\* Priority comparison: p has priority over q if p's number is smaller,
\* or if numbers are equal and p's ID is smaller
HasPriority(p, q) ==
    \/ num[q] = 0
    \/ num[p] < num[q]
    \/ (num[p] = num[q] /\ p < q)

CanEnterCS(p) ==
    \A q \in Procs \ {p}:
        /\ ~choosing[q]
        /\ HasPriority(p, q)

EnterCS(p) ==
    /\ pc[p] = "waiting"
    /\ CanEnterCS(p)
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED <<num, choosing>>

ExitCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<num, choosing>>

Reset(p) ==
    /\ pc[p] = "exit"
    /\ num' = [num EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED choosing

Next ==
    \E p \in Procs:
        \/ StartChoosing(p)
        \/ ComputeTicket(p)
        \/ FinishChoosing(p)
        \/ EnterCS(p)
        \/ ExitCS(p)
        \/ Reset(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

MutualExclusion ==
    \A p, q \in Procs: (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

Invariant == MutualExclusion

=======================================================================