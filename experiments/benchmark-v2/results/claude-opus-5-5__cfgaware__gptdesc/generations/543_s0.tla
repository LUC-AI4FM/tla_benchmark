---------------------------- MODULE MCSession7fg ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT N

ASSUME N \in Nat

VARIABLES x, pc, t

vars == << x, pc, t >>

Procs == 1..N

CS == {"p1", "p2"}

-----------------------------------------------------------------------------
(* Concurrent increment algorithm: each process enters a critical region, *)
(* reads x into its local t, then writes t + 1 back to x.                  *)

Init == /\ x = 0
        /\ t = [p \in Procs |-> 0]
        /\ pc = [p \in Procs |-> "p0"]

p0(self) == /\ pc[self] = "p0"
            /\ \A q \in Procs \ {self} : pc[q] \notin CS
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << x, t >>

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

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(proc(self))

-----------------------------------------------------------------------------
(* Model-checking definitions *)

ConstN == 3

TypeOK == /\ x \in Nat
          /\ pc \in [Procs -> {"p0", "p1", "p2", "Done"}]
          /\ t \in [Procs -> Nat]

AddCorrect == (\A p \in Procs : pc[p] = "Done") => (x = N)

ProcPairs == {pq \in Procs \X Procs : pq[1] # pq[2]}

CriticalSecInv == \A pq \in ProcPairs : ~(pc[pq[1]] \in CS /\ pc[pq[2]] \in CS)

=============================================================================