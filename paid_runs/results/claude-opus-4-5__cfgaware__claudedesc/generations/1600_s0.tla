---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT N, defaultInitValue

ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b, pc, j, failed

vars == <<x, y, b, pc, j, failed>>

Procs == 1..N

Init ==
    /\ x = defaultInitValue
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "start"]
    /\ j = [i \in Procs |-> defaultInitValue]
    /\ failed = [i \in Procs |-> FALSE]

start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "checkY"]
    /\ UNCHANGED <<y, j, failed>>

checkY(self) ==
    /\ pc[self] = "checkY"
    /\ IF y /= 0
       THEN /\ pc' = [pc EXCEPT ![self] = "backoff"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "writeY"]
    /\ UNCHANGED <<x, y, b, j, failed>>

backoff(self) ==
    /\ pc[self] = "backoff"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "waitY1"]
    /\ UNCHANGED <<x, y, j, failed>>

waitY1(self) ==
    /\ pc[self] = "waitY1"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, j, failed>>

writeY(self) ==
    /\ pc[self] = "writeY"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "checkX"]
    /\ UNCHANGED <<x, b, j, failed>>

checkX(self) ==
    /\ pc[self] = "checkX"
    /\ IF x /= self
       THEN /\ pc' = [pc EXCEPT ![self] = "clearFlag"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "enter"]
            /\ failed' = [failed EXCEPT ![self] = FALSE]
    /\ UNCHANGED <<x, y, b, j>>

clearFlag(self) ==
    /\ pc[self] = "clearFlag"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ j' = [j EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "waitFlags"]
    /\ UNCHANGED <<x, y, failed>>

waitFlags(self) ==
    /\ pc[self] = "waitFlags"
    /\ IF j[self] <= N
       THEN /\ IF j[self] /= self
               THEN /\ ~b[j[self]]
               ELSE TRUE
            /\ j' = [j EXCEPT ![self] = j[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "waitFlags"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "checkY2"]
            /\ UNCHANGED j
    /\ UNCHANGED <<x, y, b, failed>>

checkY2(self) ==
    /\ pc[self] = "checkY2"
    /\ IF y /= self
       THEN /\ pc' = [pc EXCEPT ![self] = "waitY2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "enter"]
            /\ failed' = [failed EXCEPT ![self] = FALSE]
    /\ UNCHANGED <<x, y, b, j>>

waitY2(self) ==
    /\ pc[self] = "waitY2"
    /\ y = 0
    /\ failed' = [failed EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "enter"]
    /\ UNCHANGED <<x, y, b, j>>

enter(self) ==
    /\ pc[self] = "enter"
    /\ ~failed[self]
    /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED <<x, y, b, j, failed>>

enterFailed(self) ==
    /\ pc[self] = "enter"
    /\ failed[self]
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, j, failed>>

cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<x, y, b, j, failed>>

exit(self) ==
    /\ pc[self] = "exit"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, j, failed>>

proc(self) ==
    \/ start(self)
    \/ checkY(self)
    \/ backoff(self)
    \/ waitY1(self)
    \/ writeY(self)
    \/ checkX(self)
    \/ clearFlag(self)
    \/ waitFlags(self)
    \/ checkY2(self)
    \/ waitY2(self)
    \/ enter(self)
    \/ enterFailed(self)
    \/ cs(self)
    \/ exit(self)

Next == \E self \in Procs : proc(self)

Spec == Init /\ [][Next]_vars /\ \A self \in Procs : WF_vars(proc(self))

SomeoneInCS == \E i \in Procs : pc[i] = "cs"

Contention == \E i, k \in Procs : i /= k /\ b[i] /\ b[k]

Invariant ==
    \A i, k \in Procs :
        (i /= k /\ pc[i] = "cs" /\ pc[k] = "cs") =>
            (failed[i] \/ failed[k])

Liveness == []<>SomeoneInCS

==========================================================================