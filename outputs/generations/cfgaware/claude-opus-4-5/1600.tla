---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N, defaultInitValue

ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b, pc, j, failed

vars == <<x, y, b, pc, j, failed>>

Procs == 1..N

Init == 
    /\ x = defaultInitValue
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "ncs"]
    /\ j = [i \in Procs |-> defaultInitValue]
    /\ failed = [i \in Procs |-> FALSE]

\* Non-critical section - process wants to enter critical section
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, j, failed>>

\* Start: set intent flag b[self] to TRUE
start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "setx"]
    /\ UNCHANGED <<x, y, j, failed>>

\* Set x to self
setx(self) ==
    /\ pc[self] = "setx"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "checky"]
    /\ UNCHANGED <<y, b, j, failed>>

\* Check if y is 0
checky(self) ==
    /\ pc[self] = "checky"
    /\ IF y /= 0
       THEN /\ pc' = [pc EXCEPT ![self] = "slowpath"]
            /\ failed' = [failed EXCEPT ![self] = TRUE]
       ELSE /\ pc' = [pc EXCEPT ![self] = "sety"]
            /\ failed' = [failed EXCEPT ![self] = FALSE]
    /\ UNCHANGED <<x, y, b, j>>

\* Set y to self (fast path)
sety(self) ==
    /\ pc[self] = "sety"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "checkx"]
    /\ UNCHANGED <<x, b, j, failed>>

\* Check if x is still self
checkx(self) ==
    /\ pc[self] = "checkx"
    /\ IF x /= self
       THEN /\ pc' = [pc EXCEPT ![self] = "slowpath"]
            /\ failed' = [failed EXCEPT ![self] = TRUE]
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED failed
    /\ UNCHANGED <<x, y, b, j>>

\* Slow path: check all other processes
slowpath(self) ==
    /\ pc[self] = "slowpath"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ j' = [j EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "loop"]
    /\ UNCHANGED <<x, y, failed>>

\* Loop through all processes checking their b flags
loop(self) ==
    /\ pc[self] = "loop"
    /\ IF j[self] <= N
       THEN /\ IF b[j[self]]
               THEN /\ pc' = [pc EXCEPT ![self] = "loop"]  \* wait/retry
                    /\ UNCHANGED j
               ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                    /\ pc' = [pc EXCEPT ![self] = "loop"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "checky2"]
            /\ UNCHANGED j
    /\ UNCHANGED <<x, y, b, failed>>

\* Check y again after slow path
checky2(self) ==
    /\ pc[self] = "checky2"
    /\ IF y /= self
       THEN /\ pc' = [pc EXCEPT ![self] = "ncs"]  \* restart
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED <<x, y, b, j, failed>>

\* Critical section
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<x, y, b, j, failed>>

\* Exit: reset y and b[self]
exit(self) ==
    /\ pc[self] = "exit"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<x, j, failed>>

\* Process action
proc(self) ==
    \/ ncs(self)
    \/ start(self)
    \/ setx(self)
    \/ checky(self)
    \/ sety(self)
    \/ checkx(self)
    \/ slowpath(self)
    \/ loop(self)
    \/ checky2(self)
    \/ cs(self)
    \/ exit(self)

Next == \E self \in Procs : proc(self)

Spec == Init /\ [][Next]_vars /\ \A self \in Procs : WF_vars(proc(self))

\* Mutual exclusion: at most one process in critical section
MutualExclusion == \A i, k \in Procs : (i /= k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

Invariant == MutualExclusion

\* Liveness: some process enters the critical section infinitely often
Liveness == []<>(\E self \in Procs : pc[self] = "cs")

=============================================================================