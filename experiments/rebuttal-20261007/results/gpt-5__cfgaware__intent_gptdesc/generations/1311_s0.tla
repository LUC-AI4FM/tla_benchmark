---- MODULE GCDSub ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  A,        \* fixed positive integer input
  BDomain   \* finite, nonempty set of allowed positive integers for the second input

ASSUME
  /\ A \in Nat \ {0}
  /\ BDomain \subseteq Nat \ {0}
  /\ BDomain # {}
  /\ IsFiniteSet(BDomain)

VARIABLES x, y, y0, pc

vars == << x, y, y0, pc >>

RECURSIVE GCD(_,_)
GCD(m, n) ==
  IF n = 0 THEN m
  ELSE GCD(n, m % n)

Init ==
  /\ y0 \in BDomain
  /\ x = A
  /\ y = y0
  /\ pc = "loop"

Swap ==
  /\ pc = "loop"
  /\ x > 0 /\ y > 0
  /\ x < y
  /\ x' = y
  /\ y' = x
  /\ y0' = y0
  /\ pc' = "loop"

Sub ==
  /\ pc = "loop"
  /\ x > 0 /\ y > 0
  /\ x >= y
  /\ x' = x - y
  /\ y' = y
  /\ y0' = y0
  /\ pc' = "loop"

Done ==
  /\ pc = "loop"
  /\ (x = 0 \/ y = 0)
  /\ x' = x
  /\ y' = y
  /\ y0' = y0
  /\ pc' = "done"

Next == Swap \/ Sub \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Terminated == pc = "done"

\* Invariants and properties

TypeOK ==
  /\ x \in Nat
  /\ y \in Nat
  /\ y0 \in Nat \ {0}
  /\ pc \in {"loop", "done"}

GCDInv == GCD(x, y) = GCD(A, y0)

Bounded == /\ x <= A + y0
           /\ y <= A + y0

ExitCorrect ==
  Terminated => /\ (x = 0 \/ y = 0)
                /\ (IF x = 0 THEN y = GCD(A, y0) ELSE x = GCD(A, y0))

Invariant == TypeOK /\ GCDInv /\ Bounded /\ ExitCorrect

\* Safety: never negative and always within the initial-sum bound
Safety == [](x \in Nat /\ y \in Nat /\ Bounded)

\* Liveness: the algorithm always terminates
Liveness == <> Terminated
Termination == Liveness

====