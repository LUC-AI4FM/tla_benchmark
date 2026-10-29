---------------------------- MODULE MCSession7fg ----------------------------
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

\* Concrete constant value used by TLC to override N
const_N == 3

Procs == 1..N

VARIABLES x, pc, t

vars == << x, pc, t >>

-----------------------------------------------------------------------------
(* Base algorithm (as in Session7fg)                                       *)
(* Each process waits until no process is in its critical region          *)
(* {"p1","p2"}, then reads x into its local t and writes t+1 back to x.   *)
-----------------------------------------------------------------------------

Init == /\ x = 0
        /\ t = [p \in Procs |-> 0]
        /\ pc = [p \in Procs |-> "p0"]

p0(self) == /\ pc[self] = "p0"
            /\ \A q \in Procs : pc[q] \notin {"p1", "p2"}
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << x, t >>

p1(self) == /\ pc[self] = "p1"
            /\ t' = [t EXCEPT ![self] = x]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ x' = x

p2(self) == /\ pc[self] = "p2"
            /\ x' = t[self] + 1
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ t' = t

proc(self) == p0(self) \/ p1(self) \/ p2(self)

Terminating == /\ \A self \in Procs : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs : proc(self))
        \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(proc(self))

Termination == <>(\A self \in Procs : pc[self] = "Done")

-----------------------------------------------------------------------------
(* Model-checking companion definitions                                    *)
-----------------------------------------------------------------------------

TypeOK == /\ x \in Nat
          /\ pc \in [Procs -> {"p0", "p1", "p2", "Done"}]
          /\ t \in [Procs -> Nat]

Correctness == (\A p \in Procs : pc[p] = "Done") => (x = N)

Pairs == {pr \in Procs \X Procs : pr[1] # pr[2]}

MutualExclusion ==
    \A pr \in Pairs : ~ (pc[pr[1]] \in {"p1", "p2"} /\ pc[pr[2]] \in {"p1", "p2"})

THEOREM Spec => [](TypeOK /\ Correctness /\ MutualExclusion)
=============================================================================