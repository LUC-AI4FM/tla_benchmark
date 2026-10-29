---------------------------- MODULE MCSession7fg ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat \ {0}

const_N == 3

Procs == 1..N

VARIABLES x, pc, t

vars == <<x, pc, t>>

Init ==
    /\ x = 0
    /\ t = [p \in Procs |-> 0]
    /\ pc = [p \in Procs |-> "p0"]

p0(self) ==
    /\ pc[self] = "p0"
    /\ \A q \in Procs \ {self} : pc[q] \notin {"p1", "p2"}
    /\ pc' = [pc EXCEPT ![self] = "p1"]
    /\ UNCHANGED <<x, t>>

p1(self) ==
    /\ pc[self] = "p1"
    /\ t' = [t EXCEPT ![self] = x]
    /\ pc' = [pc EXCEPT ![self] = "p2"]
    /\ UNCHANGED x

p2(self) ==
    /\ pc[self] = "p2"
    /\ x' = t[self] + 1
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED t

proc(self) == p0(self) \/ p1(self) \/ p2(self)

Terminating ==
    /\ \A self \in Procs : pc[self] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ \E self \in Procs : proc(self)
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in Procs : WF_vars(proc(self))

-----------------------------------------------------------------------------

TypeOK ==
    /\ x \in Nat
    /\ pc \in [Procs -> {"p0", "p1", "p2", "Done"}]
    /\ t \in [Procs -> Nat]

PCorrect ==
    (\A p \in Procs : pc[p] = "Done") => (x = N)

ProcPairs == {pr \in Procs \X Procs : pr[1] # pr[2]}

MutualExclusion ==
    \A pr \in ProcPairs :
        ~ (pc[pr[1]] \in {"p1", "p2"} /\ pc[pr[2]] \in {"p1", "p2"})

Termination == <>(\A p \in Procs : pc[p] = "Done")

=============================================================================