--------------------------- MODULE RegularRingRegisters ---------------------------

EXTENDS Naturals

CONSTANT N
ASSUME N \in Nat /\ N > 0

(*
N processes arranged in a ring. Each process i:
  - performs a write of 1 to its own shared register x[i] modeled as a regular register:
      {0} -> {0,1} -> {1}
  - then reads its neighbor's register x[Succ(i)], where the read returns any element
    currently in that set.
We model the regular register x[i] as a set of possible values in {{0}, {0,1}, {1}}.
*)

Proc == 1..N
Values == {0, 1}
RegisterValues == {{0}, {0,1}, {1}}

Succ(i) == IF i < N THEN i + 1 ELSE 1

(*
PlusCal-style control states:
  "w1" : first part of the write (set {0} -> {0,1})
  "w2" : second part of the write (set {0,1} -> {1})
  "r"  : read neighbor's register
  "done": finished
*)

VARIABLES pc, x, y

vars == << pc, x, y >>

TypeOK ==
  /\ pc \in [Proc -> {"w1","w2","r","done"}]
  /\ x \in [Proc -> SUBSET Values]
  /\ \A i \in Proc: x[i] \in RegisterValues
  /\ y \in [Proc -> Values]

Init ==
  /\ pc = [i \in Proc |-> "w1"]
  /\ x = [i \in Proc |-> {0}]
  /\ y = [i \in Proc |-> 0]

W1(i) ==
  /\ i \in Proc
  /\ pc[i] = "w1"
  /\ x[i] = {0}
  /\ x' = [x EXCEPT ![i] = {0,1}]
  /\ pc' = [pc EXCEPT ![i] = "w2"]
  /\ UNCHANGED y

W2(i) ==
  /\ i \in Proc
  /\ pc[i] = "w2"
  /\ x[i] = {0,1}
  /\ x' = [x EXCEPT ![i] = {1}]
  /\ pc' = [pc EXCEPT ![i] = "r"]
  /\ UNCHANGED y

R(i) ==
  /\ i \in Proc
  /\ pc[i] = "r"
  /\ x' = x
  /\ \E v \in x[Succ(i)]:
       /\ y' = [y EXCEPT ![i] = v]
       /\ pc' = [pc EXCEPT ![i] = "done"]

Next ==
  \E i \in Proc: W1(i) \/ W2(i) \/ R(i)

Spec == Init /\ [][Next]_vars

Terminated == \A i \in Proc: pc[i] = "done"

(*
Auxiliary inductive invariant capturing well-typedness and the fact that
once a process has passed its second write step, its own register is {1}.
*)
AfterW2OwnIs1 == \A i \in Proc: (pc[i] \in {"r","done"}) => x[i] = {1}

Inv == TypeOK /\ AfterW2OwnIs1

(*
Safety property (PCorrect): If all processes are done, then some read value is 1.
*)
PCorrect == Terminated => (\E i \in Proc: y[i] = 1)

(*
Proof obligations (TLAPS skeletons):
  1) Inv is an invariant of Spec.
  2) PCorrect holds under Spec (intended to be derived using Inv).
*)

THEOREM InvIsInvariant ==
  Spec => []Inv
PROOF
  OBVIOUS
QED

THEOREM Correctness ==
  Spec => []PCorrect
PROOF
  OBVIOUS
QED

=============================================================================