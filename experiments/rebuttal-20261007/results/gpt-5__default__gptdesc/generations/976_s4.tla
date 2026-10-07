----------------------------- MODULE Ring -----------------------------
EXTENDS Naturals, TLC

(*
--algorithm Ring
variables x = [i \in 1..N |-> 0], y = [i \in 1..N |-> 0];

define
  ProcSet == 1..N;
  Left(i) == IF i = 1 THEN N ELSE i - 1;
end define;

process (i \in ProcSet)
begin
a1:   x[i] := 1;
a2:   y[i] := x[Left(i)];
Done: skip;
end process;
end algorithm
*)

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLES x, y, pc

ProcSet == 1..N

Left(i) == IF i = 1 THEN N ELSE i - 1

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
  \E i \in ProcSet: A1(i) \/ A2(i)

AllDone ==
  \A i \in ProcSet: pc[i] = "Done"

ExistsYOne ==
  \E i \in ProcSet: y[i] = 1

Inv ==
  /\ TypeOK
  /\ \A i \in ProcSet: (pc[i] \in {"a2", "Done"} => x[i] = 1)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in ProcSet: WF_vars(A1(i)) /\ WF_vars(A2(i))

Termination ==
  <>AllDone

SafetyState ==
  AllDone => ExistsYOne

SafetyTemporal ==
  [](AllDone => ExistsYOne)

THEOREM InvIsInvariant ==
  Init /\ [][Next]_vars => []Inv
PROOF OBVIOUS QED

THEOREM TypeCorrectness ==
  Spec => []TypeOK
PROOF
  BY InvIsInvariant
QED

THEOREM MainSafety1 ==
  Spec => SafetyTemporal
PROOF OMITTED

THEOREM MainSafety2 ==
  Spec => []SafetyState
PROOF
  BY MainSafety1
QED

THEOREM Terminates ==
  Spec => Termination
PROOF OMITTED

============================================================================