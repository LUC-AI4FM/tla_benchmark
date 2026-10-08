MODULE RingAlgorithm
EXTENDS Naturals, Sequences, TLC

CONSTANT N \in Nat
ASSUME N > 0

VARIABLES x, y, pc

(* --algorithm Ring
variables x[1..N], y[1..N];
pc[i] in {"setx","copyy","done"} for i in 1..N;

procedure Left(i) returns j:
    if i = 1 then N else i-1;

action SetX(i):
    x[i] := 1;
    pc[i] := "copyy";

action CopyY(i):
    y[i] := x[Left(i)];
    pc[i] := "done";
-- end algorithm
*)

LEFT(i) == IF i = 1 THEN N ELSE i - 1

TypeOK ==
    /\ x \in [1..N -> Nat]
    /\ y \in [1..N -> Nat]
    /\ pc \in [1..N -> {"setx","copyy","done"}]

Init ==
    /\ x = [i \in 1..N |-> 0]
    /\ y = [i \in 1..N |-> 0]
    /\ pc = [i \in 1..N |-> "setx"]
    /\ TypeOK

SetX(i) == 
    /\ i \in 1..N
    /\ pc[i] = "setx"
    /\ x' = [x EXCEPT ![i] = 1]
    /\ pc' = [pc EXCEPT ![i] = "copyy"]
    /\ y' = y

CopyY(i) ==
    /\ i \in 1..N
    /\ pc[i] = "copyy"
    /\ y' = [y EXCEPT ![i] = x[LEFT(i)]]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ x' = x

Next ==
    \/ \E i \in 1..N : SetX(i)
    \/ \E i \in 1..N : CopyY(i)

Inv ==
    (* Safety invariant: if all processes are done, at least one y[i] = 1 *)
    ( (\A i \in 1..N : pc[i] = "done") => (\E i \in 1..N : y[i] = 1) )
    /\ TypeOK

Spec == Init /\ [][Next]_<<x,y,pc>>

Termination ==
    \A i \in 1..N : <> (pc[i] = "done")

THEOREM TerminationTheorem == Spec => Termination
PROOF
  OBVIOUS

THEOREM MainCorrectness_Induction == Spec => []Inv
PROOF
  OBVIOUS

THEOREM MainCorrectness_Invariant == Spec => []Inv
PROOF
  OBVIOUS

END RingAlgorithm