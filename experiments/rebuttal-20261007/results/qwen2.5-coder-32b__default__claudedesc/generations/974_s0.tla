------------------------------- MODULE RegularRegisterAlgorithm -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES x, y, pc

(* --algorithm RegularRegisterAlgorithm
variables 
    x = [i \in 0..N-1 |-> {0}],
    y = [i \in 0..N-1 |-> 0],
    pc = [i \in 0..N-1 |-> "a1"];

process (P \in 0..N-1)
begin
a1:
    x[P] := {0, 1};
    pc[P] := "a2";
a2:
    x[P] := {1};
    pc[P] := "b";
b:
    y[P] := CHOOSE v \in x[(P - 1) % N];
    pc[P] := "Done";
end process; *)
=============================================================================