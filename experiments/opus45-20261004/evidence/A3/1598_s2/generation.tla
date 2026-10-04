---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS N

ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b, S, pc

Procs == 1..N

TypeOK ==
    /\ x \in Procs \cup {0}
    /\ y \in Procs \cup {0}
    /\ b \in [Procs -> BOOLEAN]
    /\ S \in [Procs -> SUBSET Procs]
    /\ pc \in [Procs -> {"ncs", "start", "setx", "checkx", "sety", "checky", 
                         "wait", "cs", "exit", "reset"}]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ S = [i \in Procs |-> {}]
    /\ pc = [i \in Procs |-> "ncs"]

\* Non-critical section - process decides to enter critical section
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, S>>

\* Start - set b[self] to TRUE
start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "setx"]
    /\ UNCHANGED <<x, y, S>>

\* Set x to self
setx(self) ==
    /\ pc[self] = "setx"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "checkx"]
    /\ UNCHANGED <<y, b, S>>

\* Check if y != 0, if so retry
checkx(self) ==
    /\ pc[self] = "checkx"
    /\ IF y /= 0
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ S' = [S EXCEPT ![self] = {i \in Procs : b[i]}]
            /\ pc' = [pc EXCEPT ![self] = "wait"]
            /\ UNCHANGED <<x, y>>
       ELSE /\ pc' = [pc EXCEPT ![self] = "sety"]
            /\ UNCHANGED <<x, y, b, S>>

\* Wait for y to become 0, then restart
wait(self) ==
    /\ pc[self] = "wait"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, S>>

\* Set y to self
sety(self) ==
    /\ pc[self] = "sety"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "checky"]
    /\ UNCHANGED <<x, b, S>>

\* Check if x = self, otherwise wait for others
checky(self) ==
    /\ pc[self] = "checky"
    /\ IF x = self
       THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED <<x, y, b, S>>
       ELSE /\ b' = [b EXCEPT ![self] = FALSE]
            /\ S' = [S EXCEPT ![self] = {i \in Procs : b[i]}]
            /\ pc' = [pc EXCEPT ![self] = "waitall"]
            /\ UNCHANGED <<x, y>>

\* Wait for all processes in S to set b to FALSE
waitall(self) ==
    /\ pc[self] = "waitall"
    /\ \A i \in S[self] : ~b[i]
    /\ IF y = self
       THEN pc' = [pc EXCEPT ![self] = "cs"]
       ELSE pc' = [pc EXCEPT ![self] = "recheck"]
    /\ UNCHANGED <<x, y, b, S>>

\* Recheck y and possibly restart
recheck(self) ==
    /\ pc[self] = "recheck"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, S>>

\* Critical section
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<x, y, b, S>>

\* Exit - reset y and b[self]
exit(self) ==
    /\ pc[self] = "exit"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<x, S>>

\* Combined action for process self
proc(self) ==
    \/ ncs(self)
    \/ start(self)
    \/ setx(self)
    \/ checkx(self)
    \/ wait(self)
    \/ sety(self)
    \/ checky(self)
    \/ waitall(self)
    \/ recheck(self)
    \/ cs(self)
    \/ exit(self)

Next ==
    \E self \in Procs : proc(self)

vars == <<x, y, b, S, pc>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety: Mutual Exclusion - no two distinct processes in CS simultaneously
MutualExclusion ==
    \A i, j \in Procs : (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Liveness: Infinitely often some process is in the critical section
SomeoneInCS ==
    \E i \in Procs : pc[i] = "cs"

Liveness == []<>SomeoneInCS

=============================================================================