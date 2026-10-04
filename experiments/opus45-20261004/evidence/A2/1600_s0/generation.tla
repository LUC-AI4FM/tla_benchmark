---------------------------- MODULE FastMutex ----------------------------
EXTENDS Naturals, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, b, pc, j, failed

vars == <<x, y, b, pc, j, failed>>

Procs == 1..N

TypeOK ==
    /\ x \in Procs \cup {0}
    /\ y \in Procs \cup {0}
    /\ b \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> {"ncs", "start", "checkY", "writeY", "checkX", 
                         "clearFlag", "waitFlags", "checkYAgain", "waitY",
                         "cs", "exit"}]
    /\ j \in [Procs -> Procs \cup {0, N+1}]
    /\ failed \in [Procs -> BOOLEAN]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "ncs"]
    /\ j = [i \in Procs |-> 0]
    /\ failed = [i \in Procs |-> FALSE]

ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ failed' = [failed EXCEPT ![self] = FALSE]
    /\ UNCHANGED <<x, y, b, j>>

start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "checkY"]
    /\ UNCHANGED <<y, j, failed>>

checkY(self) ==
    /\ pc[self] = "checkY"
    /\ IF y /= 0
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "waitY"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "writeY"]
            /\ UNCHANGED b
    /\ UNCHANGED <<x, y, j, failed>>

writeY(self) ==
    /\ pc[self] = "writeY"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "checkX"]
    /\ UNCHANGED <<x, b, j, failed>>

checkX(self) ==
    /\ pc[self] = "checkX"
    /\ IF x /= self
       THEN /\ pc' = [pc EXCEPT ![self] = "clearFlag"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED <<x, y, b, j, failed>>

clearFlag(self) ==
    /\ pc[self] = "clearFlag"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ j' = [j EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "waitFlags"]
    /\ UNCHANGED <<x, y, failed>>

waitFlags(self) ==
    /\ pc[self] = "waitFlags"
    /\ IF j[self] <= N
       THEN IF j[self] /= self /\ b[j[self]]
            THEN UNCHANGED <<x, y, b, pc, j, failed>>
            ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                 /\ UNCHANGED <<x, y, b, pc, failed>>
       ELSE /\ pc' = [pc EXCEPT ![self] = "checkYAgain"]
            /\ UNCHANGED <<x, y, b, j, failed>>

checkYAgain(self) ==
    /\ pc[self] = "checkYAgain"
    /\ IF y /= self
       THEN /\ pc' = [pc EXCEPT ![self] = "waitY"]
            /\ failed' = [failed EXCEPT ![self] = TRUE]
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED failed
    /\ UNCHANGED <<x, y, b, j>>

waitY(self) ==
    /\ pc[self] = "waitY"
    /\ IF y /= 0
       THEN UNCHANGED <<x, y, b, pc, j, failed>>
       ELSE /\ pc' = [pc EXCEPT ![self] = "ncs"]
            /\ UNCHANGED <<x, y, b, j, failed>>

cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<x, y, b, j, failed>>

exit(self) ==
    /\ pc[self] = "exit"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<x, j, failed>>

proc(self) ==
    \/ ncs(self)
    \/ start(self)
    \/ checkY(self)
    \/ writeY(self)
    \/ checkX(self)
    \/ clearFlag(self)
    \/ waitFlags(self)
    \/ checkYAgain(self)
    \/ waitY(self)
    \/ cs(self)
    \/ exit(self)

Next == \E self \in Procs : proc(self)

Fairness == \A self \in Procs : WF_vars(proc(self))

Spec == Init /\ [][Next]_vars /\ Fairness

InCS(i) == pc[i] = "cs" /\ ~failed[i]

Invariant == \A i, k \in Procs : i /= k => ~(InCS(i) /\ InCS(k))

SomeoneInCS == \E i \in Procs : pc[i] = "cs"

Liveness == []<>SomeoneInCS

Contention == \E i, k \in Procs : i /= k /\ pc[i] = "cs" /\ pc[k] \in {"checkX", "clearFlag", "waitFlags", "checkYAgain", "waitY"}

==========================================================================