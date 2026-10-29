---------------------------- MODULE MCSession7fg ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

\* Concrete constant value used to instantiate N during model checking
const_N == 3

Procs == 1..N

VARIABLES x, pc, t

vars == <<x, pc, t>>

-----------------------------------------------------------------------------
(* Underlying algorithm (corresponding to Session7fg)                       *)
(* Each process enters a guarded region (p1, p2), reads x into its local    *)
(* t, then writes t + 1 back to x, and finishes in "Done".                  *)

Init ==
    /\ x = 0
    /\ t = [p \in Procs |-> 0]
    /\ pc = [p \in Procs |-> "p0"]

p0(self) ==
    /\ pc[self] = "p0"
    /\ \A q \in Procs : pc[q] \notin {"p1", "p2"}
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

Next == (\E self \in Procs : proc(self)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(proc(self))

-----------------------------------------------------------------------------
(* Model-checking companion definitions                                     *)

TypeOK ==
    /\ x \in Nat
    /\ pc \in [Procs -> {"p0", "p1", "p2", "Done"}]
    /\ t \in [Procs -> Nat]

\* If all processes have finished, x equals N
Correctness ==
    (\A p \in Procs : pc[p] = "Done") => (x = N)

\* Set of pairs of distinct processes
ProcPairs == {pr \in Procs \X Procs : pr[1] # pr[2]}

\* No two different processes are simultaneously in the region {p1, p2}
MutualExclusion ==
    \A pr \in ProcPairs :
        ~ (pc[pr[1]] \in {"p1", "p2"} /\ pc[pr[2]] \in {"p1", "p2"})

\* Liveness: eventually all processes are done
Termination == <>(\A p \in Procs : pc[p] = "Done")

THEOREM Spec => [](TypeOK /\ Correctness /\ MutualExclusion)
=============================================================================