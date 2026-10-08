----------------------------- MODULE Euclid -----------------------------
EXTENDS Naturals

(*
  Euclidean algorithm (subtraction-and-swap form) for gcd(A, B).
  - A is a fixed positive integer constant.
  - B is chosen nondeterministically as b0 in 1..N at initialization.
  - State variables x, y carry the current pair.
  - Loop step: if x < y then swap, else subtract y from x.
  - Halting when one component is zero; the other equals gcd(A, b0).
*)

CONSTANTS A, N

ASSUME /\ A \in Nat \ {0}
       /\ N \in Nat \ {0}

VARIABLES x, y, b0

vars == << x, y, b0 >>

Done == (x = 0) \/ (y = 0)

Init ==
  /\ b0 \in 1..N
  /\ x = A
  /\ y = b0

Swap ==
  /\ x < y
  /\ x' = y
  /\ y' = x
  /\ UNCHANGED b0

Sub ==
  /\ x >= y
  /\ y > 0
  /\ x' = x - y
  /\ y' = y
  /\ UNCHANGED b0

Loop ==
  /\ ~Done
  /\ IF x < y THEN Swap ELSE Sub

Next == Loop

Spec == Init /\ [][Next]_vars /\ WF_vars(Loop)

(*
  Recursive definition of gcd used for invariants/correctness only.
  Uses modulo; not used by the algorithmic transitions.
*)
RECURSIVE GCD(_, _)
GCD(m, n) == IF n = 0 THEN m ELSE GCD(n, m % n)

Sum == x + y

TypeInv ==
  /\ x \in Nat
  /\ y \in Nat
  /\ b0 \in 1..N

PositivityInv ==
  /\ ~Done => /\ x \in Nat \ {0}
              /\ y \in Nat \ {0}

BoundInv ==
  /\ Sum <= A + b0
  /\ Sum \in Nat

GcdInv ==
  GCD(x, y) = GCD(A, b0)

SafetyInv == TypeInv /\ PositivityInv /\ BoundInv

CorrectAtHalt ==
  Done =>
    /\ (x = 0 => /\ y = GCD(A, b0) /\ y \in Nat \ {0})
    /\ (y = 0 => /\ x = GCD(A, b0) /\ x \in Nat \ {0})

(*
  Liveness property: under weak fairness of Loop, the algorithm eventually halts.
  TLC can check Spec => Termination by setting Spec as the behavior and Termination as property.
*)
Termination == <>Done

============================================================================