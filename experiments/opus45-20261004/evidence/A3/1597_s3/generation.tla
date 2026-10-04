-------------------------------- MODULE FastMutex --------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N

ASSUME N >= 2

VARIABLES x, y, b, pc, failed

vars == <<x, y, b, pc, failed>>

Procs == 1..N

ProcStates == {"ncs", "start", "setx", "checkb", "sety", "checky", "checkx", "wait", "cs", "exit", "reset"}

TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> ProcStates]
    /\ failed \in [Procs -> BOOLEAN]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "ncs"]
    /\ failed = [i \in Procs |-> FALSE]

\* Non-critical section - process decides to enter
NCS(self) ==
    /\ pc[self] = "ncs"
    /\ ~failed[self]
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, failed>>

\* Start: set b[self] to TRUE
Start(self) ==
    /\ pc[self] = "start"
    /\ ~failed[self]
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "setx"]
    /\ UNCHANGED <<x, y, failed>>

\* Set x to self
SetX(self) ==
    /\ pc[self] = "setx"
    /\ ~failed[self]
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "checkb"]
    /\ UNCHANGED <<y, b, failed>>

\* Check if y != 0, if so go back to start (slow path)
CheckB(self) ==
    /\ pc[self] = "checkb"
    /\ ~failed[self]
    /\ IF y /= 0
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "wait"]
            /\ UNCHANGED <<x, y, failed>>
       ELSE /\ pc' = [pc EXCEPT ![self] = "sety"]
            /\ UNCHANGED <<x, y, b, failed>>

\* Set y to self
SetY(self) ==
    /\ pc[self] = "sety"
    /\ ~failed[self]
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "checky"]
    /\ UNCHANGED <<x, b, failed>>

\* Check if x = self (fast path succeeded)
CheckY(self) ==
    /\ pc[self] = "checky"
    /\ ~failed[self]
    /\ IF x = self
       THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED <<x, y, b, failed>>
       ELSE /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "checkx"]
            /\ UNCHANGED <<x, y, failed>>

\* Slow path: wait for all other b[j] to be FALSE
CheckX(self) ==
    /\ pc[self] = "checkx"
    /\ ~failed[self]
    /\ \A j \in Procs : j /= self => ~b[j]
    /\ IF y = self
       THEN pc' = [pc EXCEPT ![self] = "cs"]
       ELSE pc' = [pc EXCEPT ![self] = "wait"]
    /\ UNCHANGED <<x, y, b, failed>>

\* Wait for y to become 0, then restart
Wait(self) ==
    /\ pc[self] = "wait"
    /\ ~failed[self]
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, failed>>

\* Critical section - process can exit
CS(self) ==
    /\ pc[self] = "cs"
    /\ ~failed[self]
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<x, y, b, failed>>

\* Exit: reset y and b[self]
Exit(self) ==
    /\ pc[self] = "exit"
    /\ ~failed[self]
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<x, failed>>

\* Process failure - can fail at any point except in CS
Fail(self) ==
    /\ pc[self] /= "cs"
    /\ ~failed[self]
    /\ failed' = [failed EXCEPT ![self] = TRUE]
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ IF y = self THEN y' = 0 ELSE y' = y
    /\ IF x = self THEN x' = 0 ELSE x' = x
    /\ UNCHANGED pc

\* Recovery from failure
Recover(self) ==
    /\ failed[self]
    /\ failed' = [failed EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<x, y, b>>

\* Process 1 step
Proc1Step ==
    \/ NCS(1)
    \/ Start(1)
    \/ SetX(1)
    \/ CheckB(1)
    \/ SetY(1)
    \/ CheckY(1)
    \/ CheckX(1)
    \/ Wait(1)
    \/ CS(1)
    \/ Exit(1)
    \/ Fail(1)
    \/ Recover(1)

\* Process i (2..N) step
ProcIStep(self) ==
    \/ NCS(self)
    \/ Start(self)
    \/ SetX(self)
    \/ CheckB(self)
    \/ SetY(self)
    \/ CheckY(self)
    \/ CheckX(self)
    \/ Wait(self)
    \/ CS(self)
    \/ Exit(self)
    \/ Fail(self)
    \/ Recover(self)

OtherProcsStep ==
    \E self \in 2..N : ProcIStep(self)

Next ==
    \/ Proc1Step
    \/ OtherProcsStep

\* Weak fairness for process 1
Fairness1 ==
    /\ WF_vars(NCS(1))
    /\ WF_vars(Start(1))
    /\ WF_vars(SetX(1))
    /\ WF_vars(CheckB(1))
    /\ WF_vars(SetY(1))
    /\ WF_vars(CheckY(1))
    /\ WF_vars(CheckX(1))
    /\ WF_vars(Wait(1))
    /\ WF_vars(CS(1))
    /\ WF_vars(Exit(1))

\* Weak fairness for processes 2..N
FairnessOther ==
    \A self \in 2..N :
        /\ WF_vars(NCS(self))
        /\ WF_vars(Start(self))
        /\ WF_vars(SetX(self))
        /\ WF_vars(CheckB(self))
        /\ WF_vars(SetY(self))
        /\ WF_vars(CheckY(self))
        /\ WF_vars(CheckX(self))
        /\ WF_vars(Wait(self))
        /\ WF_vars(CS(self))
        /\ WF_vars(Exit(self))

Fairness == Fairness1 /\ FairnessOther

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Mutual Exclusion - no two distinct processes are simultaneously in CS
MutualExclusion ==
    \A i, j \in Procs : (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Liveness: Infinitely often some process is in the critical section
SomeoneInCS == \E i \in Procs : pc[i] = "cs"
Liveness == []<>SomeoneInCS

===============================================================================