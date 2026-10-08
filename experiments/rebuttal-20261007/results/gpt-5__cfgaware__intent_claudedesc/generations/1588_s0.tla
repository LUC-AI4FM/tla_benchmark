----------------------------- MODULE Euclid24 -----------------------------
EXTENDS Integers, TLC

CONSTANT N
ASSUME N \in Nat \ {0}

VARIABLES a, b, b0, printed

vars == << a, b, b0, printed >>

RECURSIVE GCD(_,_)

GCD(m, n) ==
  IF n = 0 THEN m ELSE GCD(n, m % n)

A == 24

Init ==
  /\ a = A
  /\ b \in 1..N
  /\ b0 = b
  /\ printed = FALSE

Done == (a = 0) \/ (b = 0)

Result == IF a = 0 THEN b ELSE a

AgtB ==
  /\ ~Done
  /\ a >= b
  /\ b > 0
  /\ a' = a - b
  /\ b' = b
  /\ b0' = b0
  /\ printed' = printed

BgtA ==
  /\ ~Done
  /\ b > a
  /\ a > 0
  /\ b' = b - a
  /\ a' = a
  /\ b0' = b0
  /\ printed' = printed

Emit ==
  /\ Done
  /\ ~printed
  /\ UNCHANGED << a, b, b0 >>
  /\ PrintT([ aFixed |-> A,
               bOriginal |-> b0,
               result |-> Result,
               specGCD |-> GCD(A, b0),
               ok |-> (Result = GCD(A, b0)) ], TRUE)
  /\ printed' = TRUE

Next == AgtB \/ BgtA \/ Emit

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(AgtB)
  /\ WF_vars(BgtA)
  /\ WF_vars(Emit)

Correct ==
  Done => Result = GCD(A, b0)

Termination == <>printed
=============================