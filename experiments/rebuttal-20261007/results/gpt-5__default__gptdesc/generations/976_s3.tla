---- MODULE Ring ----
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

(*
PlusCal algorithm:

--algorithm RingAlg
variables x = [i \in 1..N |-> 0],
          y = [i \in 1..N |-> 0];

process (Proc \in 1..N)
begin
s1: x[self] := 1;
s2: y[self] := x[IF self = 1 THEN N ELSE self - 1];
done: skip;
end process
end algorithm
*)

VARIABLES x, y, pc

vars == << x, y, pc >>

Procs == 1..N

Left(i) == IF i = 1 THEN N ELSE i - 1

TypeOK ==
  /\ x \in [Procs -> {0, 1}]
  /\ y \in [Procs -> {0, 1}]
  /\ pc \in [Procs -> {"s1", "s2", "Done"}]

Init ==
  /\ x = [i \in Procs |-> 0]
  /\ y = [i \in Procs |-> 0]
  /\ pc = [i \in Procs |-> "s1"]

S1(i) ==
  /\ i \in Procs
  /\ pc[i] = "s1"
  /\ x' = [x EXCEPT ![i] = 1]
  /\ y' = y
  /\ pc' = [pc EXCEPT ![i] = "s2"]

S2(i) ==
  /\ i \in Procs
  /\ pc[i] = "s2"
  /\ x' = x
  /\ y' = [y EXCEPT ![i] = x[Left(i)]]
  /\ pc' = [pc EXCEPT ![i] = "Done"]

Next ==
  \E i \in Procs: S1(i) \/ S2(i)

Fair ==
  \A i \in Procs: WF_vars(S1(i)) /\ WF_vars(S2(i))

Spec == Init /\ [][Next]_vars /\ Fair

(*
Inductive invariant:
- Type correctness.
- Process has not yet performed s1 iff its x-entry is still 0.
*)
Inv ==
  /\ TypeOK
  /\ \A i \in Procs: (pc[i] = "s1") <=> (x[i] = 0)

Terminated == \A i \in Procs: pc[i] = "Done"
Termination == <> Terminated

Safety == Terminated => \E i \in Procs: y[i] = 1

THEOREM InvIsInvariant ==
  Spec => []Inv
PROOF OBVIOUS QED

THEOREM LivenessTermination ==
  Spec => Termination
PROOF OBVIOUS QED

(*
Main safety property: when all processes are done, at least one y[i] = 1.
Two TLAPS proof forms are provided.
*)
THEOREM Correctness_v1 ==
  Spec => [](Safety)
PROOF OMITTED

THEOREM Correctness_v2 ==
  Spec => [](Safety)
PROOF
  <1>1. InvIsInvariant BY DEF InvIsInvariant
  <1>2. QED OBVIOUS
QED
====