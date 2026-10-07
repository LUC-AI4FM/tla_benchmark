----------------------------- MODULE Ring -----------------------------

EXTENDS Naturals, TLC

(*
This PlusCal algorithm models a simple concurrent ring with N processes.
Each process i first sets x[i] := 1, then copies its left neighbor's x
into y[i]. Processes are arranged in a circle 1..N, with Left(i) = IF i=1 THEN N ELSE i-1.
We assume N is a positive natural number.

--algorithm ring
variables x = [i \in 1..N |-> 0],
          y = [i \in 1..N |-> 0];

fair process (self \in 1..N)
variable i = self;
begin
a: x[i] := 1;
b: y[i] := x[IF i = 1 THEN N ELSE i - 1];
end process;

end algorithm
*)

CONSTANT N

ASSUME NIsPositive == N \in Nat \ {0}

Procs == 1..N
Bits  == {0, 1}
Labels == {"a", "b", "Done"}

Left(i) == IF i = 1 THEN N ELSE i - 1

VARIABLES x, y, pc

vars == << x, y, pc >>

(***************************************************************************)
(* BEGIN TRANSLATION (of the PlusCal algorithm above)                      *)
(***************************************************************************)

Init ==
  /\ x = [i \in Procs |-> 0]
  /\ y = [i \in Procs |-> 0]
  /\ pc = [i \in Procs |-> "a"]

A(i) ==
  /\ i \in Procs
  /\ pc[i] = "a"
  /\ x'  = [x EXCEPT ![i] = 1]
  /\ UNCHANGED y
  /\ pc' = [pc EXCEPT ![i] = "b"]

B(i) ==
  /\ i \in Procs
  /\ pc[i] = "b"
  /\ UNCHANGED x
  /\ y'  = [y EXCEPT ![i] = x[Left(i)]]
  /\ pc' = [pc EXCEPT ![i] = "Done"]

Proc(i) == A(i) \/ B(i)

Next == \E i \in Procs : Proc(i)

Fairness == \A i \in Procs : WF_vars(Proc(i))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* END TRANSLATION                                                         *)
(***************************************************************************)

TypeOK ==
  /\ x \in [Procs -> Bits]
  /\ y \in [Procs -> Bits]
  /\ pc \in [Procs -> Labels]

Inv ==
  /\ TypeOK
  /\ \A i \in Procs : (pc[i] \in {"b","Done"} => x[i] = 1)
  /\ \A i \in Procs : (pc[i] = "a" => y[i] = 0)

AllDone == \A i \in Procs : pc[i] = "Done"

Termination == <>AllDone

Safety ==
  [] (AllDone => (\E i \in Procs : y[i] = 1))

THEOREM TypeCorrectness ==
  Spec => []TypeOK
PROOF OMITTED

THEOREM InvIsInvariant ==
  Spec => []Inv
PROOF OMITTED

THEOREM TerminationThm ==
  Spec => Termination
PROOF OMITTED

THEOREM MainCorrectness1 ==
  Spec => Safety
PROOF OMITTED

Correctness2 ==
  AllDone ~> (\E i \in Procs : y[i] = 1)

THEOREM MainCorrectness2 ==
  Spec => Correctness2
PROOF OMITTED

=============================================================================