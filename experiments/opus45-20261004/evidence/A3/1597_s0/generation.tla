------------------------------ MODULE FastMutex ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N

ASSUME N >= 2

VARIABLES x, y, b, pc, failed

vars == <<x, y, b, pc, failed>>

Procs == 1..N

ProcSet == Procs

(* Process control states *)
States == {"ncs", "start", "setx", "checkb", "sety", "checky", "checkx", "wait", "cs", "exit", "resetb"}

TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> States]
    /\ failed \in [Procs -> BOOLEAN]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "ncs"]
    /\ failed = [i \in Procs |-> FALSE]

(* Non-critical section - process may proceed to start *)
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ ~failed[self]
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, failed>>

(* Start - set b[self] to TRUE *)
start(self) ==
    /\ pc[self] = "start"
    /\ ~failed[self]
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "setx"]
    /\ UNCHANGED <<x, y, failed>>

(* Set x to self *)
setx(self) ==
    /\ pc[self] = "setx"
    /\ ~failed[self]
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "checkb"]
    /\ UNCHANGED <<y, b, failed>>

(* Check if y is 0 *)
checkb(self) ==
    /\ pc[self] = "checkb"
    /\ ~failed[self]
    /\ IF y /= 0
       THEN pc' = [pc EXCEPT ![self] = "wait"]
       ELSE pc' = [pc EXCEPT ![self] = "sety"]
    /\ UNCHANGED <<x, y, b, failed>>

(* Set y to self *)
sety(self) ==
    /\ pc[self] = "sety"
    /\ ~failed[self]
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "checky"]
    /\ UNCHANGED <<x, b, failed>>

(* Check if x equals self *)
checky(self) ==
    /\ pc[self] = "checky"
    /\ ~failed[self]
    /\ IF x /= self
       THEN pc' = [pc EXCEPT ![self] = "checkx"]
       ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED <<x, y, b, failed>>

(* Wait for other processes' b flags and check y *)
checkx(self) ==
    /\ pc[self] = "checkx"
    /\ ~failed[self]
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "wait"]
    /\ UNCHANGED <<x, y, failed>>

(* Wait state - check y and other processes *)
wait(self) ==
    /\ pc[self] = "wait"
    /\ ~failed[self]
    /\ IF y = 0
       THEN pc' = [pc EXCEPT ![self] = "start"]
       ELSE IF y = self
            THEN pc' = [pc EXCEPT ![self] = "cs"]
            ELSE IF ~b[y] \/ failed[y]
                 THEN pc' = [pc EXCEPT ![self] = "start"]
                 ELSE pc' = [pc EXCEPT ![self] = "wait"]
    /\ UNCHANGED <<x, y, b, failed>>

(* Critical section - process is in CS *)
cs(self) ==
    /\ pc[self] = "cs"
    /\ ~failed[self]
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<x, y, b, failed>>

(* Exit critical section - reset y *)
exit(self) ==
    /\ pc[self] = "exit"
    /\ ~failed[self]
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![self] = "resetb"]
    /\ UNCHANGED <<x, b, failed>>

(* Reset b flag *)
resetb(self) ==
    /\ pc[self] = "resetb"
    /\ ~failed[self]
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<x, y, failed>>

(* Process failure - can fail at any time except in CS *)
fail(self) ==
    /\ ~failed[self]
    /\ pc[self] /= "cs"
    /\ failed' = [failed EXCEPT ![self] = TRUE]
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ IF y = self
       THEN y' = 0
       ELSE y' = y
    /\ UNCHANGED <<x, pc>>

(* Process recovery *)
recover(self) ==
    /\ failed[self]
    /\ failed' = [failed EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<x, y, b>>

(* Process 1 actions (distinguished process) *)
Proc1 ==
    \/ ncs(1)
    \/ start(1)
    \/ setx(1)
    \/ checkb(1)
    \/ sety(1)
    \/ checky(1)
    \/ checkx(1)
    \/ wait(1)
    \/ cs(1)
    \/ exit(1)
    \/ resetb(1)

(* Family of processes 2..N *)
ProcN(self) ==
    \/ ncs(self)
    \/ start(self)
    \/ setx(self)
    \/ checkb(self)
    \/ sety(self)
    \/ checky(self)
    \/ checkx(self)
    \/ wait(self)
    \/ cs(self)
    \/ exit(self)
    \/ resetb(self)

Next ==
    \/ Proc1
    \/ \E self \in 2..N : ProcN(self)
    \/ \E self \in Procs : fail(self)
    \/ \E self \in Procs : recover(self)

(* Weak fairness for process 1 *)
Fairness1 ==
    /\ WF_vars(ncs(1))
    /\ WF_vars(start(1))
    /\ WF_vars(setx(1))
    /\ WF_vars(checkb(1))
    /\ WF_vars(sety(1))
    /\ WF_vars(checky(1))
    /\ WF_vars(checkx(1))
    /\ WF_vars(wait(1))
    /\ WF_vars(cs(1))
    /\ WF_vars(exit(1))
    /\ WF_vars(resetb(1))

(* Weak fairness for processes 2..N *)
FairnessN ==
    \A self \in 2..N :
        /\ WF_vars(ncs(self))
        /\ WF_vars(start(self))
        /\ WF_vars(setx(self))
        /\ WF_vars(checkb(self))
        /\ WF_vars(sety(self))
        /\ WF_vars(checky(self))
        /\ WF_vars(checkx(self))
        /\ WF_vars(wait(self))
        /\ WF_vars(cs(self))
        /\ WF_vars(exit(self))
        /\ WF_vars(resetb(self))

Fairness == Fairness1 /\ FairnessN

Spec == Init /\ [][Next]_vars /\ Fairness

(* Safety invariant: Mutual Exclusion *)
MutualExclusion ==
    \A i, j \in Procs : (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(* Liveness property: Infinitely often some process is in CS *)
Liveness == []<>(\E i \in Procs : pc[i] = "cs")

=============================================================================