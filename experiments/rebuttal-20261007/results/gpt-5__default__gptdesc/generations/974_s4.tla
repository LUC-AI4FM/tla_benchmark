----------------------------- MODULE RegularRing -----------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 1

(*
Processes are 1..N arranged on a ring. Each process i:
  - performs a regular-register write of its own x[i] from 0 to 1 by:
       {0} -> {0,1} -> {1}
  - then reads its neighbor's register x[Nb(i)] into y[i], where the read may
    nondeterministically return any element currently in that set.
*)

Proc == 1..N
Vals == {0, 1}
RegVals == SUBSET Vals

Nb(i) == IF i < N THEN i + 1 ELSE 1

VARIABLES pc, x, y

vars == << pc, x, y >>

TypeOK ==
  /\ pc \in [Proc -> {"w0", "w1", "r", "Done"}]
  /\ x \in [Proc -> RegVals]
  /\ y \in [Proc -> Vals]

Init ==
  /\ TypeOK
  /\ pc = [i \in Proc |-> "w0"]
  /\ x  = [i \in Proc |-> {0}]
  /\ y  = [i \in Proc |-> 0]

WriteExpand(i) ==
  /\ i \in Proc
  /\ pc[i] = "w0"
  /\ x[i] = {0}
  /\ pc' = [pc EXCEPT ![i] = "w1"]
  /\ x'  = [x  EXCEPT ![i] = {0, 1}]
  /\ y' = y

WriteCommit(i) ==
  /\ i \in Proc
  /\ pc[i] = "w1"
  /\ x[i] = {0, 1}
  /\ pc' = [pc EXCEPT ![i] = "r"]
  /\ x'  = [x  EXCEPT ![i] = {1}]
  /\ y' = y

Read(i) ==
  /\ i \in Proc
  /\ pc[i] = "r"
  /\ LET j == Nb(i) IN
       \E v \in x[j]:
         /\ y' = [y EXCEPT ![i] = v]
  /\ pc' = [pc EXCEPT ![i] = "Done"]
  /\ x' = x

Step(i) == WriteExpand(i) \/ WriteCommit(i) \/ Read(i)

Next == \E i \in Proc: Step(i)

(*
Termination condition: all processes have finished.
*)
Termination == \A i \in Proc: pc[i] = "Done"

(*
Safety property: If all processes are done, then some read y[i] equals 1.
*)
PCorrect == Termination => (\E i \in Proc: y[i] = 1)

(*
Inductive invariant used to reason about correctness.
It captures types and the coupling between control state and register contents.
*)
Inv ==
  /\ TypeOK
  /\ \A i \in Proc:
       /\ (pc[i] = "w0")  => x[i] = {0}
       /\ (pc[i] = "w1")  => x[i] = {0, 1}
       /\ (pc[i] \in {"r", "Done"}) => x[i] = {1}

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Proc: WF_vars(Step(i))

=============================================================================