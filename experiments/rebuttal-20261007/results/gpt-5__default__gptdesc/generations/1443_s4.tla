---- MODULE Mod3Counter ----
EXTENDS Integers, TLC

CONSTANTS DummyConst

VARIABLES x

vars == << x >>

(* Helper predicates and action, labeled for TLC coverage *)
IsOne == IsOneL :: x = 1
WorkDone == WorkDoneL :: x = 2
Wrap == WrapL :: x = 2 /\ x' = 0

Init == x = 0

Step01 == x = 0 /\ x' = 1
Step12 == x = 1 /\ x' = 2

Next == Step01 \/ Step12 \/ Wrap

TypeOK == x \in {0, 1, 2}
StateCover == (x = 0) \/ IsOne \/ WorkDone

Spec == Init /\ [][Next]_vars

(* TLC-specific coverage check: expect each labeled predicate to be counted once *)
CoverageOK ==
  LET cov == TLCGet("coverage")
  IN /\ cov["IsOneL"] = 1
     /\ cov["WorkDoneL"] = 1
     /\ cov["WrapL"] = 1

CoverageAssert == Assert(CoverageOK, "Expected each named predicate to be covered once")

====