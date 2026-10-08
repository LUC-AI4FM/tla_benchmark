----------------------------- MODULE Clock12 -----------------------------
EXTENDS Integers

CONSTANTS HOURMOD
ASSUME HOURMOD = 12

VARIABLES h

HourSet == 1..HOURMOD

NextOf(i) == IF i < HOURMOD THEN i + 1 ELSE 1
NextOfMod(i) == (i \mod HOURMOD) + 1

TypeOK == h \in HourSet

Init == TypeOK

StepInc ==
  /\ TypeOK
  /\ h' = NextOf(h)

StepMod ==
  /\ TypeOK
  /\ h' = NextOfMod(h)

Next == StepInc

Spec ==
  /\ Init
  /\ [][Next]_h
  /\ WF_h(Next)

(*
 Safety properties
*)
AlwaysValid == [] (h \in HourSet)

AlwaysEnabled == [] ENABLED Next

(*
 Liveness properties
*)
ProgressToSuccessor ==
  \A i \in HourSet : [] (h = i => <> (h = NextOf(i)))

RecurringAllHours ==
  \A i \in HourSet : []<>(h = i)

(*
 Equivalence properties between the stepwise and modular transitions
*)
EquivNonStutterInvariant ==
  (TypeOK /\ TypeOK') => (UNCHANGED h \/ (StepInc <=> StepMod))

EquivStutteringTemporal ==
  [] ( [StepInc]_h <=> [StepMod]_h )

AltSpec ==
  /\ Init
  /\ [][StepMod]_h
  /\ WF_h(StepMod)

(*
 Theorems (no proofs included)
*)
THEOREM NextOfEq == \A i \in HourSet : NextOf(i) = NextOfMod(i)
THEOREM SpecEquiv == Spec <=> AltSpec
THEOREM SafetyHolds == Spec => AlwaysValid
THEOREM FairEnabled == Spec => AlwaysEnabled
THEOREM EquivalenceHolds == Spec => [] EquivNonStutterInvariant
THEOREM ProgressHolds == Spec => ProgressToSuccessor
THEOREM RecurrenceHolds == Spec => RecurringAllHours
=============================================================================