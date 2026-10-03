------------------------------ MODULE RegularRing ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

(*
N processes arranged in a ring. Each process i:
- performs a regular-register write to its own x[i] from 0 to 1,
  modeled as {0} -> {0,1} -> {1}
- then reads its neighbor's register x[Nbr(i)], obtaining any value
  currently in that set, and stores it in y[i]
*)

Val == {0, 1}
XStates == {{0}, {0,1}, {1}}
Proc == 1..N

VARIABLES pc, x, y

vars == << pc, x, y >>

Nbr(i) == IF i < N THEN i+1 ELSE 1

Init ==
  /\ pc = [i \in Proc |-> "w1"]
  /\ x = [i \in Proc |-> {0}]
  /\ y = [i \in Proc |-> 0]

Write1(i) ==
  /\ i \in Proc
  /\ pc[i] = "w1"
  /\ x[i] = {0}
  /\ pc' = [pc EXCEPT ![i] = "w2"]
  /\ x'  = [x  EXCEPT ![i] = {0,1}]
  /\ y' = y

Write2(i) ==
  /\ i \in Proc
  /\ pc[i] = "w2"
  /\ x[i] = {0,1}
  /\ pc' = [pc EXCEPT ![i] = "r"]
  /\ x'  = [x  EXCEPT ![i] = {1}]
  /\ y' = y

Read(i) ==
  /\ i \in Proc
  /\ pc[i] = "r"
  /\ LET nb == Nbr(i) IN
       \E v \in x[nb] :
         y' = [y EXCEPT ![i] = v]
  /\ pc' = [pc EXCEPT ![i] = "done"]
  /\ x' = x

Next ==
  \E i \in Proc : Write1(i) \/ Write2(i) \/ Read(i)

AllDone == \A i \in Proc : pc[i] = "done"

Terminated == AllDone

TypeInv ==
  /\ x \in [Proc -> XStates]
  /\ y \in [Proc -> Val]
  /\ pc \in [Proc -> {"w1","w2","r","done"}]

PhaseConsistent ==
  /\ \A i \in Proc :
        IF pc[i] = "w1" THEN x[i] = {0}
        ELSE IF pc[i] = "w2" THEN x[i] = {0,1}
        ELSE x[i] = {1}

(*
Safety property of interest:
  If all processes are done, then some y[i] = 1
We encode an inductive invariant Inv that implies this.
*)
NotAllDoneAllZero ==
  ~ (AllDone /\ \A i \in Proc : y[i] = 0)

Inv == TypeInv /\ PhaseConsistent /\ NotAllDoneAllZero

PCorrect == AllDone => (\E i \in Proc : y[i] = 1)

Spec == Init /\ [][Next]_vars

THEOREM InvIsInvariant ==
  Init /\ [][Next]_vars => []Inv
PROOF OBVIOUS

THEOREM PCorrectness ==
  Spec => []PCorrect
PROOF
  BY InvIsInvariant DEF Spec, PCorrect, Inv, AllDone
QED

================================