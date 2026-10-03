---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT N

ASSUME N >= 2

VARIABLES x, y, b, pc, failed

vars == <<x, y, b, pc, failed>>

Procs == 1..N

TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [1..N -> BOOLEAN]
    /\ pc \in [1..N -> {"ncs", "start", "setx", "checkb", "sety", "checkx", 
                        "checky", "wait", "cs", "exit", "reset"}]
    /\ failed \in [1..N -> BOOLEAN]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in 1..N |-> FALSE]
    /\ pc = [i \in 1..N |-> "ncs"]
    /\ failed = [i \in 1..N |-> FALSE]

\* Non-critical section - process decides to enter
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ ~failed[self]
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, failed>>

\* Start of fast path - set b[self] to TRUE
start(self) ==
    /\ pc[self] = "start"
    /\ ~failed[self]
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "setx"]
    /\ UNCHANGED <<x, y, failed>>

\* Set x to self
setx(self) ==
    /\ pc[self] = "setx"
    /\ ~failed[self]
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "checkb"]
    /\ UNCHANGED <<y, b, failed>>

\* Check if y is 0
checkb(self) ==
    /\ pc[self] = "checkb"
    /\ ~failed[self]
    /\ IF y /= 0
       THEN pc' = [pc EXCEPT ![self] = "checky"]
       ELSE pc' = [pc EXCEPT ![self] = "sety"]
    /\ UNCHANGED <<x, y, b, failed>>

\* Set y to self (fast path)
sety(self) ==
    /\ pc[self] = "sety"
    /\ ~failed[self]
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "checkx"]
    /\ UNCHANGED <<x, b, failed>>

\* Check if x is still self
checkx(self) ==
    /\ pc[self] = "checkx"
    /\ ~failed[self]
    /\ IF x /= self
       THEN pc' = [pc EXCEPT ![self] = "wait"]
       ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED <<x, y, b, failed>>

\* Wait for other processes to finish
wait(self) ==
    /\ pc[self] = "wait"
    /\ ~failed[self]
    /\ \A j \in 1..N \ {self} : b[j] = FALSE
    /\ IF y = self
       THEN pc' = [pc EXCEPT ![self] = "cs"]
       ELSE pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<x, y, b, failed>>

\* Slow path - check y
checky(self) ==
    /\ pc[self] = "checky"
    /\ ~failed[self]
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "reset"]
    /\ UNCHANGED <<x, y, failed>>

\* Reset and wait for y to become 0
reset(self) ==
    /\ pc[self] = "reset"
    /\ ~failed[self]
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, failed>>

\* Critical section
cs(self) ==
    /\ pc[self] = "cs"
    /\ ~failed[self]
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<x, y, b, failed>>

\* Exit critical section
exit(self) ==
    /\ pc[self] = "exit"
    /\ ~failed[self]
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<x, failed>>

\* Process failure (can happen at any time except in CS)
fail(self) ==
    /\ pc[self] /= "cs"
    /\ ~failed[self]
    /\ failed' = [failed EXCEPT ![self] = TRUE]
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ IF y = self THEN y' = 0 ELSE y' = y
    /\ IF x = self THEN x' = 0 ELSE x' = x

\* Recovery from failure
recover(self) ==
    /\ failed[self]
    /\ failed' = [failed EXCEPT ![self] = FALSE]
    /\ UNCHANGED <<x, y, b, pc>>

\* Process 1 (distinguished process)
Proc1 ==
    \/ ncs(1)
    \/ start(1)
    \/ setx(1)
    \/ checkb(1)
    \/ sety(1)
    \/ checkx(1)
    \/ wait(1)
    \/ checky(1)
    \/ reset(1)
    \/ cs(1)
    \/ exit(1)
    \/ fail(1)
    \/ recover(1)

\* Processes 2..N
ProcN(self) ==
    \/ ncs(self)
    \/ start(self)
    \/ setx(self)
    \/ checkb(self)
    \/ sety(self)
    \/ checkx(self)
    \/ wait(self)
    \/ checky(self)
    \/ reset(self)
    \/ cs(self)
    \/ exit(self)
    \/ fail(self)
    \/ recover(self)

Next ==
    \/ Proc1
    \/ \E self \in 2..N : ProcN(self)

\* Weak fairness for process 1
Fairness1 ==
    /\ WF_vars(ncs(1))
    /\ WF_vars(start(1))
    /\ WF_vars(setx(1))
    /\ WF_vars(checkb(1))
    /\ WF_vars(sety(1))
    /\ WF_vars(checkx(1))
    /\ WF_vars(wait(1))
    /\ WF_vars(checky(1))
    /\ WF_vars(reset(1))
    /\ WF_vars(cs(1))
    /\ WF_vars(exit(1))

\* Weak fairness for processes 2..N
FairnessN ==
    \A self \in 2..N :
        /\ WF_vars(ncs(self))
        /\ WF_vars(start(self))
        /\ WF_vars(setx(self))
        /\ WF_vars(checkb(self))
        /\ WF_vars(sety(self))
        /\ WF_vars(checkx(self))
        /\ WF_vars(wait(self))
        /\ WF_vars(checky(self))
        /\ WF_vars(reset(self))
        /\ WF_vars(cs(self))
        /\ WF_vars(exit(self))

Fairness == Fairness1 /\ FairnessN

Spec == Init /\ [][Next]_vars /\ Fairness

\* Mutual exclusion: no two distinct processes in CS simultaneously
MutualExclusion ==
    \A i, j \in 1..N : (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Invariant == MutualExclusion

\* Liveness: infinitely often some process is in the critical section
Liveness == []<>(\E i \in 1..N : pc[i] = "cs")

==========================================================================