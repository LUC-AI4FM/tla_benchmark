------------------------------- MODULE EuclidGCD -------------------------------

EXTENDS Naturals, Integers

CONSTANTS A, N

ASSUME A \in Nat /\ A > 0
ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b0

vars == << x, y, b0 >>

Term == (x = 0) \/ (y = 0)

Init ==
  /\ b0 \in 1..N
  /\ x = A
  /\ y = b0

Swap ==
  /\ ~Term
  /\ x < y
  /\ x' = y
  /\ y' = x
  /\ b0' = b0

Subtract ==
  /\ ~Term
  /\ x >= y
  /\ y > 0
  /\ x' = x - y
  /\ y' = y
  /\ b0' = b0

Next == Swap \/ Subtract

(*
  Auxiliary math for correctness/invariants
*)
CommonDivs(m, n) == { d \in 1..(m + n) : (m % d) = 0 /\ (n % d) = 0 }

MaxElt(S) == CHOOSE d \in S : \A e \in S : e <= d

GCD(m, n) ==
  IF m = 0 /\ n = 0 THEN 0
  ELSE MaxElt(CommonDivs(m, n))

(*
  Safety and invariant properties
*)
TypeOK ==
  /\ x \in Nat /\ y \in Nat
  /\ b0 \in 1..N

BoundsOK ==
  /\ x <= A + b0
  /\ y <= A + b0

NoZeroBeforeTerm == ~Term => (x > 0 /\ y > 0)

GCDInvariant == GCD(x, y) = GCD(A, b0)

SafetyInv == TypeOK /\ BoundsOK /\ NoZeroBeforeTerm /\ (x + y > 0)

(*
  Liveness and correctness properties
*)
Termination == <> Term

CorrectAtTermination ==
  [] ( Term => ((x = 0 /\ y = GCD(A, b0)) \/ (y = 0 /\ x = GCD(A, b0))) )

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Swap)
  /\ WF_vars(Subtract)

===============================================================================