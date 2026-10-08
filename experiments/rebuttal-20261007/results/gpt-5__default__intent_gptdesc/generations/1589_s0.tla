------------------------------ MODULE EuclidGCD ------------------------------

EXTENDS Naturals, Integers, TLC

CONSTANT N
ASSUME N \in Nat \ {0}

VARIABLES x, y, x0, y0

vars == << x, y, x0, y0 >>

Max2(a, b) == IF a >= b THEN a ELSE b

Divisors(a, b) ==
  { d \in 1..Max2(a, b) : (a % d) = 0 /\ (b % d) = 0 }

GCD(a, b) ==
  CHOOSE g \in Divisors(a, b) : \A d \in Divisors(a, b) : d <= g

Init ==
  /\ x \in 1..N
  /\ y \in 1..N
  /\ x0 = x
  /\ y0 = y

Terminated == (x = 0) \/ (y = 0)

Swap ==
  /\ x > 0 /\ y > 0
  /\ x < y
  /\ x' = y
  /\ y' = x

SubtractX ==
  /\ y > 0
  /\ x >= y
  /\ x' = x - y
  /\ y' = y

SubtractY ==
  /\ x > 0
  /\ y > x
  /\ y' = y - x
  /\ x' = x

Subtract == SubtractX \/ SubtractY

Next ==
  /\ (Swap \/ Subtract)
  /\ UNCHANGED << x0, y0 >>

Spec ==
  Init /\ [][Next]_vars /\ SF_vars(Subtract)

(*
 Safety invariants
*)
TypeInv ==
  /\ x \in 0..N
  /\ y \in 0..N
  /\ x0 \in 1..N
  /\ y0 \in 1..N
  /\ ~(x = 0 /\ y = 0)

PosUntilTerminated ==
  ~Terminated => (x > 0 /\ y > 0)

GCDInvariant ==
  GCD(x, y) = GCD(x0, y0)

CorrectOnTerminate ==
  Terminated => (IF x = 0 THEN y ELSE x) = GCD(x0, y0)

Inv == TypeInv /\ PosUntilTerminated /\ GCDInvariant /\ CorrectOnTerminate

(*
 Action-level preservation of correctness
*)
SwapPreserves ==
  Swap => GCD(x', y') = GCD(x, y)

SubtractPreserves ==
  Subtract => GCD(x', y') = GCD(x, y)

(*
 Liveness: eventual termination
*)
Termination == <> Terminated

=============================================================================