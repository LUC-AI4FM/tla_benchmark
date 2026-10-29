---------------------------- MODULE MCSession7fg ----------------------------
EXTENDS Integers, Naturals, TLC

CONSTANT N

ASSUME N \in Nat \ {0}

(* Concrete constant value to substitute for N when model checking *)
constN == 3

Procs == 1..N

VARIABLES x, pc, t

vars == <<x, pc, t>>

-----------------------------------------------------------------------------
(* Algorithm: each process enters a critical region (p1, p2) only when    *)
(* no other process is in it, reads x into local t, then writes t + 1.    *)
-----------------------------------------------------------------------------

Init == /\ x = 0
        /\ t = [p \in Procs |-> 0]
        /\ pc = [p \in Procs |-> "p0"]

p0(self) == /\ pc[self] = "p0"
            /\ \A q \in Procs \ {self} : pc[q] \notin {"p1", "p2"}
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED <<x, t>>

p1(self) == /\ pc[self] = "p1"
            /\ t' = [t EXCEPT ![self] = x]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED x

p2(self) == /\ pc[self] = "p2"
            /\ x' = t[self] + 1
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED t

proc(self) == p0(self) \/ p1(self) \/ p2(self)

Terminating == /\ \A self \in Procs : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs : proc(self)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(proc(self))

-----------------------------------------------------------------------------
(* Invariants and properties                                              *)
-----------------------------------------------------------------------------

TypeOK == /\ x \in Nat
          /\ pc \in [Procs -> {"p0", "p1", "p2", "Done"}]
          /\ t \in [Procs -> Nat]

Correctness == (\A p \in Procs : pc[p] = "Done") => (x = N)

Pairs == {pq \in Procs \X Procs : pq[1] # pq[2]}

MutualExclusion ==
    \A pq \in Pairs :
        ~ (pc[pq[1]] \in {"p1", "p2"} /\ pc[pq[2]] \in {"p1", "p2"})

Termination == <>(\A p \in Procs : pc[p] = "Done")

=============================================================================