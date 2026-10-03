------------------------------ MODULE Ring ------------------------------

EXTENDS Naturals

(*
--algorithm RingAlgorithm
variables x = [i \in ProcSet |-> 0],
          y = [i \in ProcSet |-> 0];

define {
  Left(i) == IF i = 1 THEN N ELSE i - 1;
}

process (i \in ProcSet)
variables xi \in {0,1}, yi \in {0,1};
begin
a1: x[i] := 1;
a2: y[i] := x[Left(i)];
done: skip;
end process
end algorithm;
*)

CONSTANT N

ASSUME N \in Nat \ {0}

ProcSet == 1..N

Left(i) == IF i = 1 THEN N ELSE i - 1

VARIABLES x, y, pc

vars == << x, y, pc >>

TypeOK ==
  /\ x \in [ProcSet -> {0, 1}]
  /\ y \in [ProcSet -> {0, 1}]
  /\ pc \in [ProcSet -> {"a1", "a2", "Done"}]

Init ==
  /\ x = [i \in ProcSet |-> 0]
  /\ y = [i \in ProcSet |-> 0]
  /\ pc = [i \in ProcSet |-> "a1"]

A1(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "a1"
  /\ x'  = [x EXCEPT ![i] = 1]
  /\ y'  = y
  /\ pc' = [pc EXCEPT ![i] = "a2"]

A2(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "a2"
  /\ x'  = x
  /\ y'  = [y EXCEPT ![i] = x[Left(i)]]
  /\ pc' = [pc EXCEPT ![i] = "Done"]

Next ==
  \E i \in ProcSet:
    A1(i) \/ A2(i)

AllDone == \A i \in ProcSet: pc[i] = "Done"

Termination == <> AllDone

Safety == [](AllDone => \E i \in ProcSet: y[i] = 1)

Fairness ==
  /\ \A i \in ProcSet: WF_vars(A1(i))
  /\ \A i \in ProcSet: WF_vars(A2(i))

Spec == Init /\ [][Next]_vars /\ Fairness

Inv ==
  /\ TypeOK
  /\ \A i \in ProcSet:
        /\ (pc[i] = "a1" => x[i] = 0)
        /\ (pc[i] \in {"a2", "Done"} => x[i] = 1)

THEOREM TypeOkInvariant ==
  Spec => []TypeOK
PROOF OMITTED

THEOREM InvIsInvariant ==
  Spec => []Inv
PROOF OMITTED

THEOREM TerminationThm ==
  Spec => Termination
PROOF OMITTED

THEOREM Correctness_v1 ==
  Spec => Safety
PROOF OMITTED

THEOREM Correctness_v2 ==
  Spec => [](AllDone => \E i \in ProcSet: y[i] = 1)
PROOF OMITTED

=============================================================================