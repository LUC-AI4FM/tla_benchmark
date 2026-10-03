----------------------------- MODULE Ring -----------------------------
EXTENDS Naturals

(*
--algorithm RingAlgo
variables
  x = [i \in 0..(N-1) |-> 0],
  y = [i \in 0..(N-1) |-> 0];

process (Proc \in 0..(N-1))
begin
a0: x[self] := 1;
a1: y[self] := x[IF self = 0 THEN N-1 ELSE self - 1];
end process;

end algorithm
*)

CONSTANT N

ASSUME N \in Nat \ {0}

ProcSet == 0..(N-1)

Labels == {"a0", "a1", "Done"}

Left(i) == IF i = 0 THEN N - 1 ELSE i - 1

VARIABLES x, y, pc

vars == << x, y, pc >>

TypeOK ==
  /\ x \in [ProcSet -> {0, 1}]
  /\ y \in [ProcSet -> {0, 1}]
  /\ pc \in [ProcSet -> Labels]

Init ==
  /\ x = [i \in ProcSet |-> 0]
  /\ y = [i \in ProcSet |-> 0]
  /\ pc = [i \in ProcSet |-> "a0"]

A0(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "a0"
  /\ x' = [x EXCEPT ![i] = 1]
  /\ y' = y
  /\ pc' = [pc EXCEPT ![i] = "a1"]

A1(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "a1"
  /\ x' = x
  /\ y' = [y EXCEPT ![i] = x[Left(i)]]
  /\ pc' = [pc EXCEPT ![i] = "Done"]

Next ==
  \E i \in ProcSet: A0(i) \/ A1(i)

Fairness ==
  \A i \in ProcSet: WF_vars(A0(i)) /\ WF_vars(A1(i))

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

AllDone == \A i \in ProcSet: pc[i] = "Done"

OneY == \E i \in ProcSet: y[i] = 1

Safety == [](AllDone => OneY)

Termination == <> AllDone

Inv ==
  /\ TypeOK
  /\ \A i \in ProcSet: (pc[i] # "a0") => x[i] = 1

PCorrect == Termination /\ Safety

THEOREM InitImpliesInv ==
  Init => Inv
PROOF OBVIOUS QED

THEOREM InvIsInductive ==
  Inv /\ Next => Inv'
PROOF OBVIOUS QED

THEOREM InvIsInvariant ==
  Spec => []Inv
PROOF
  BY InitImpliesInv, InvIsInductive DEF Spec, Init, Next, Inv, vars
QED

THEOREM TypeOKIsInvariant ==
  Spec => []TypeOK
PROOF
  BY InvIsInvariant DEF Inv
QED

THEOREM SafetyThm ==
  Spec => Safety
PROOF OBVIOUS QED

THEOREM TerminationThm ==
  Spec => Termination
PROOF OBVIOUS QED

THEOREM PCorrect_v1 ==
  Spec => []TypeOK /\ PCorrect
PROOF
  BY TypeOKIsInvariant, SafetyThm, TerminationThm DEF PCorrect
QED

THEOREM PCorrect_v2 ==
  Spec => []TypeOK /\ (Termination /\ Safety)
PROOF
  BY PCorrect_v1 DEF PCorrect
QED

=============================================================================