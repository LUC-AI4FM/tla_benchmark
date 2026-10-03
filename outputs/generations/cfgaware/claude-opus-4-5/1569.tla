---------------------------- MODULE bakery ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT NumProcs, MaxNum

ASSUME NumProcs \in Nat /\ NumProcs > 0
ASSUME MaxNum \in Nat /\ MaxNum > 0

Procs == 1..NumProcs

VARIABLES num, choosing, pc, localRead, localMax, localJ

vars == <<num, choosing, pc, localRead, localMax, localJ>>

TypeOK ==
    /\ num \in [Procs -> Nat]
    /\ choosing \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> {"ncs", "start", "read", "choose", "wait", "check", "cs", "exit"}]
    /\ localRead \in [Procs -> [Procs -> Nat]]
    /\ localMax \in [Procs -> Nat]
    /\ localJ \in [Procs -> 1..(NumProcs+1)]

Init ==
    /\ num = [p \in Procs |-> 0]
    /\ choosing = [p \in Procs |-> FALSE]
    /\ pc = [p \in Procs |-> "ncs"]
    /\ localRead = [p \in Procs |-> [q \in Procs |-> 0]]
    /\ localMax = [p \in Procs |-> 0]
    /\ localJ = [p \in Procs |-> 1]

NCS(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<num, choosing, localRead, localMax, localJ>>

Start(self) ==
    /\ pc[self] = "start"
    /\ choosing' = [choosing EXCEPT ![self] = TRUE]
    /\ localRead' = [localRead EXCEPT ![self] = num]
    /\ localMax' = [localMax EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "read"]
    /\ UNCHANGED <<num, localJ>>

Read(self) ==
    /\ pc[self] = "read"
    /\ LET maxVal == LET S == {localRead[self][q] : q \in Procs}
                     IN IF S = {} THEN 0
                        ELSE CHOOSE x \in S : \A y \in S : x >= y
       IN localMax' = [localMax EXCEPT ![self] = maxVal]
    /\ pc' = [pc EXCEPT ![self] = "choose"]
    /\ UNCHANGED <<num, choosing, localRead, localJ>>

Choose(self) ==
    /\ pc[self] = "choose"
    /\ num' = [num EXCEPT ![self] = localMax[self] + 1]
    /\ choosing' = [choosing EXCEPT ![self] = FALSE]
    /\ localJ' = [localJ EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "wait"]
    /\ UNCHANGED <<localRead, localMax>>

Wait(self) ==
    /\ pc[self] = "wait"
    /\ IF localJ[self] > NumProcs
       THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED localJ
       ELSE /\ pc' = [pc EXCEPT ![self] = "check"]
            /\ UNCHANGED localJ
    /\ UNCHANGED <<num, choosing, localRead, localMax>>

Check(self) ==
    /\ pc[self] = "check"
    /\ localJ[self] <= NumProcs
    /\ LET j == localJ[self]
       IN /\ ~choosing[j]
          /\ \/ num[j] = 0
             \/ num[self] < num[j]
             \/ (num[self] = num[j] /\ self < j)
    /\ localJ' = [localJ EXCEPT ![self] = localJ[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "wait"]
    /\ UNCHANGED <<num, choosing, localRead, localMax>>

CS(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<num, choosing, localRead, localMax, localJ>>

Exit(self) ==
    /\ pc[self] = "exit"
    /\ num' = [num EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<choosing, localRead, localMax, localJ>>

Step(self) ==
    \/ NCS(self)
    \/ Start(self)
    \/ Read(self)
    \/ Choose(self)
    \/ Wait(self)
    \/ Check(self)
    \/ CS(self)
    \/ Exit(self)

Next == \E self \in Procs : Step(self)

Spec == Init /\ [][Next]_vars /\ \A self \in Procs : WF_vars(Step(self))

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

Invariant == MutualExclusion

StateConstraint == \A p \in Procs : num[p] <= MaxNum

=======================================================================