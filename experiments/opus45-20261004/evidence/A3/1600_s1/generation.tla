---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, TLAPS, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, b, pc, j, failed

vars == <<x, y, b, pc, j, failed>>

ProcSet == 1..N

Init == 
    /\ x = 0
    /\ y = 0
    /\ b = [i \in ProcSet |-> FALSE]
    /\ pc = [self \in ProcSet |-> "ncs"]
    /\ j = [self \in ProcSet |-> 1]
    /\ failed = [self \in ProcSet |-> FALSE]

\* Non-critical section - process decides to try entering CS
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

\* Check if x still equals self
checkx(self) ==
    /\ pc[self] = "checkx"
    /\ IF x /= self
       THEN /\ pc' = [pc EXCEPT ![self] = "slowpath"]
            /\ failed' = [failed EXCEPT ![self] = TRUE]
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED failed
    /\ UNCHANGED <<x, y, b, j>>

\* Slow path: reset b[self] and prepare to check others
slowpath(self) ==
    /\ pc[self] = "slowpath"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ j' = [j EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "checkothers"]
    /\ UNCHANGED <<x, y, failed>>

\* Check all other processes' b flags
checkothers(self) ==
    /\ pc[self] = "checkothers"
    /\ IF j[self] <= N
       THEN /\ IF b[j[self]]
               THEN /\ pc' = [pc EXCEPT ![self] = "waitforb"]
               ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                    /\ pc' = pc
            /\ UNCHANGED <<x, y, b, failed>>
       ELSE /\ pc' = [pc EXCEPT ![self] = "checky2"]
            /\ UNCHANGED <<x, y, b, j, failed>>

\* Wait for b[j] to become FALSE
waitforb(self) ==
    /\ pc[self] = "waitforb"
    /\ ~b[j[self]]
    /\ j' = [j EXCEPT ![self] = j[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "checkothers"]
    /\ UNCHANGED <<x, y, b, failed>>

\* Check if y equals self after slow path
checky2(self) ==
    /\ pc[self] = "checky2"
    /\ IF y = self
       THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "waitfory"]
    /\ UNCHANGED <<x, y, b, j, failed>>

\* Wait for y to become 0, then retry
waitfory(self) ==
    /\ pc[self] = "waitfory"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
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

\* Per-process action
proc(self) ==
    \/ ncs(self)
    \/ start(self)
    \/ setx(self)
    \/ checky(self)
    \/ sety(self)
    \/ checkx(self)
    \/ slowpath(self)
    \/ checkothers(self)
    \/ waitforb(self)
    \/ checky2(self)
    \/ waitfory(self)
    \/ cs(self)
    \/ exit(self)

Next == \E self \in ProcSet : proc(self)

\* Weak fairness for every process action
Spec == Init /\ [][Next]_vars /\ \A self \in ProcSet : WF_vars(proc(self))

\* Type invariant
TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [ProcSet -> BOOLEAN]
    /\ pc \in [ProcSet -> {"ncs", "start", "setx", "checky", "sety", 
                           "checkx", "slowpath", "checkothers", "waitforb",
                           "checky2", "waitfory", "cs", "exit"}]
    /\ j \in [ProcSet -> 1..(N+1)]
    /\ failed \in [ProcSet -> BOOLEAN]

\* Mutual exclusion: at most one process in the critical section
MutualExclusion == \A i, k \in ProcSet : (pc[i] = "cs" /\ pc[k] = "cs") => i = k

\* Liveness: some process enters the critical section infinitely often
Liveness == []<>(\E self \in ProcSet : pc[self] = "cs")

==========================================================================