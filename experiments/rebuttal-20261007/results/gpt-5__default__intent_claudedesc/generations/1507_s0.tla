---- MODULE BooleanClockRecursiveCoverage ----
EXTENDS Naturals

CONSTANTS Kinit, Kcon, Kinv

ASSUME Kinit \in Nat /\ Kcon \in Nat /\ Kinv \in Nat

VARIABLES clk

RECURSIVE InitClock(_)
InitClock(k) ==
  IF k = 0 THEN FALSE
  ELSE ~InitClock(k - 1)

RECURSIVE StateOK(_, _)
StateOK(c, k) ==
  IF k = 0 THEN c \in BOOLEAN
  ELSE /\ c \in BOOLEAN
       /\ StateOK(c, k - 1)

RECURSIVE BoolOK(_, _)
BoolOK(c, k) ==
  IF k = 0 THEN c \in BOOLEAN
  ELSE BoolOK(c, k - 1)

Init ==
  clk = InitClock(Kinit)

Next ==
  clk' = ~clk

Constraint ==
  StateOK(clk, Kcon)

TypeInvariant ==
  BoolOK(clk, Kinv)

Spec ==
  /\ Init
  /\ []Next
  /\ []Constraint

THEOREM TypeSafety ==
  Spec => []TypeInvariant
====