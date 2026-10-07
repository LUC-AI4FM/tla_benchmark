----------------------------- MODULE Ring -----------------------------
EXTENDS Naturals

CONSTANT N

(*
--algorithm RingAlg
variables x = [i \in 0..(N-1) |-> 0],
          y = [i \in 0..(N-1) |-> 0];

fair process (p \in 0..(N-1))
variable self = p;
begin
L1:   x[self] := 1;
L2:   y[self] := x[IF self = 0 THEN N-1 ELSE self - 1];
Done: skip;
end process;

end algorithm
*)

ASSUME N \in Nat /\ N >= 1

VARIABLES x, y, pc

Procs == 0..(N - 1)

Left(i) == IF i = 0 THEN N - 1 ELSE i - 1

vars == << x, y, pc >>

TypeOK ==
  /\ x \in [Procs -> {0, 1}]
  /\ y \in [Procs -> {0, 1}]
  /\ pc \in [Procs -> {"L1", "L2", "Done"}]

Inv ==
  /\ TypeOK
  /\ \A i \in Procs: (pc[i] \in {"L2", "Done"} => x[i] = 1)

Init ==
  /\ x = [i \in Procs |-> 0]
  /\ y = [i \in Procs |-> 0]
  /\ pc = [i \in Procs |-> "L1"]

L1(i) ==
  /\ i \in Procs
  /\ pc[i] = "L1"
  /\ x'  = [x EXCEPT ![i] = 1]
  /\ y'  = y
  /\ pc' = [pc EXCEPT ![i] = "L2"]

L2(i) ==
  /\ i \in Procs
  /\ pc[i] = "L2"
  /\ x'  = x
  /\ y'  = [y EXCEPT ![i] = x[Left(i)]]
  /\ pc' = [pc EXCEPT ![i] = "Done"]

Proc(i) == L1(i) \/ L2(i)

Next == \E i \in Procs: Proc(i)

Done == pc = [i \in Procs |-> "Done"]

Termination == <> Done

Safety == Done => (\E i \in Procs: y[i] = 1)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Procs: WF_vars(Proc(i))

THEOREM TypeCorrectness ==
  Spec => []TypeOK
PROOF OMITTED

THEOREM InvIsInvariant ==
  Spec => []Inv
PROOF OMITTED

THEOREM TerminationThm ==
  Spec => Termination
PROOF OMITTED

THEOREM SafetyThm1 ==
  Spec => [](Safety)
PROOF OMITTED

THEOREM SafetyThm2 ==
  Spec => (Termination => <>(\E i \in Procs: y[i] = 1))
PROOF OMITTED

=============================================================================