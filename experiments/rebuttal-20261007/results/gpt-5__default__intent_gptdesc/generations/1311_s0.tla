------------------------------ MODULE GCDSubtraction ------------------------------

EXTENDS Naturals

CONSTANTS A, BMax

(*
  A: fixed positive integer (first input)
  BMax: positive bound for nondeterministic second input (second input chosen from 1..BMax)
*)
ASSUME /\ A \in Nat \ {0}
       /\ BMax \in Nat \ {0}

VARIABLES x, y, pc, x0, y0

vars == << x, y, pc, x0, y0 >>

RECURSIVE GCD(_,_)
GCD(m, n) == IF n = 0 THEN m ELSE GCD(n, m % n)

Terminated == pc = "done"

Init ==
  /\ x = A
  /\ y \in 1..BMax
  /\ x0 = x
  /\ y0 = y
  /\ pc = "loop"

Swap ==
  /\ pc = "loop"
  /\ x > 0 /\ y > 0
  /\ x < y
  /\ x' = y
  /\ y' = x
  /\ pc' = "loop"
  /\ UNCHANGED << x0, y0 >>

Sub ==
  /\ pc = "loop"
  /\ x > 0 /\ y > 0
  /\ x >= y
  /\ x' = x - y
  /\ y' = y
  /\ pc' = "loop"
  /\ UNCHANGED << x0, y0 >>

Done ==
  /\ pc = "loop"
  /\ (x = 0 \/ y = 0)
  /\ pc' = "done"
  /\ UNCHANGED << x, y, x0, y0 >>

Act == Swap \/ Sub \/ Done

Next == Act

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Safety invariants                                                        *)
(***************************************************************************)

TypeOK ==
  /\ x \in Nat
  /\ y \in Nat
  /\ pc \in {"loop","done"}
  /\ x0 \in Nat
  /\ y0 \in Nat

NonNeg ==
  /\ x \in Nat
  /\ y \in Nat

Bounded ==
  /\ x <= x0 + y0
  /\ y <= x0 + y0

GCDPreserved ==
  GCD(x, y) = GCD(x0, y0)

AtExitGCD ==
  Terminated =>
    ((x = 0 /\ y = GCD(x0, y0)) \/ (y = 0 /\ x = GCD(x0, y0)))

Safety ==
  [](NonNeg /\ Bounded)

GCDInvariant ==
  []GCDPreserved

ExitCorrectness ==
  []AtExitGCD

(***************************************************************************)
(* Liveness                                                                 *)
(***************************************************************************)

Termination ==
  <>Terminated

=============================================================================