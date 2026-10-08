---- MODULE EuclidGCD ----
EXTENDS Naturals, Integers

CONSTANT N

ASSUME N \in Nat /\ N >= 1

VARIABLES x, y, y0, printed, res, out

vars == << x, y, y0, printed, res, out >>

RECURSIVE GCD(_, _)
GCD(m, n) ==
  IF n = 0 THEN m
  ELSE GCD(n, m % n)

Done == (x = 0) \/ (y = 0)

Init ==
  /\ x = 24
  /\ y \in 1..N
  /\ y0 = y
  /\ printed = FALSE
  /\ res = 0
  /\ out = << 0, 0 >>

SubX ==
  /\ ~Done
  /\ x > y
  /\ x' = x - y
  /\ UNCHANGED << y, y0, printed, res, out >>

SubY ==
  /\ ~Done
  /\ y > x
  /\ y' = y - x
  /\ UNCHANGED << x, y0, printed, res, out >>

EqualStep ==
  /\ ~Done
  /\ x = y
  /\ x > 0
  /\ \/ /\ x' = 0
        /\ UNCHANGED << y, y0, printed, res, out >>
     \/ /\ y' = 0
        /\ UNCHANGED << x, y0, printed, res, out >>

Print ==
  /\ Done
  /\ ~printed
  /\ LET r == IF x = 0 THEN y ELSE x IN
       /\ res' = r
       /\ out' = << y0, r >>
  /\ printed' = TRUE
  /\ UNCHANGED << x, y, y0 >>

Next == SubX \/ SubY \/ EqualStep \/ Print

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

TypeOK ==
  /\ x \in Nat
  /\ y \in Nat
  /\ y0 \in 1..N
  /\ printed \in BOOLEAN
  /\ res \in Nat
  /\ out \in Nat \X Nat

InvGCD ==
  GCD(x, y) = GCD(24, y0)

ResultCorrect ==
  printed => /\ Done
             /\ res = GCD(24, y0)
             /\ out = << y0, res >>
             /\ ( (x = 0 /\ y = res) \/ (y = 0 /\ x = res) )

Termination ==
  <> printed
====