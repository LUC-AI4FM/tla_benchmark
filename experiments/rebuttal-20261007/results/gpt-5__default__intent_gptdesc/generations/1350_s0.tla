------------------------------- MODULE CounterMachine -------------------------------

EXTENDS Naturals, Integers

CONSTANTS StartVal, MaxVal
ASSUME StartVal = 1 /\ MaxVal = 5

VARIABLES c

vars == << c >>

Init ==
  c = StartVal

Inc ==
  /\ c < MaxVal
  /\ c' = c + 1

Fixed ==
  /\ c = MaxVal
  /\ c' = c

Next ==
  Inc \/ Fixed

Spec ==
  /\ Init
  /\ []Next
  /\ SF_vars(Inc)

(*
  Safety invariants and properties
*)

TypeInvariant ==
  c \in StartVal .. MaxVal

BoundsAlways ==
  []TypeInvariant

NoDecrease ==
  [](c' >= c)

NoBigJumps ==
  [](c' <= c + 1)

StepDiscipline ==
  /\ []( (c < MaxVal) => (c' = c + 1) )
  /\ []( (c = MaxVal) => (c' = c) )

Safety ==
  /\ BoundsAlways
  /\ StepDiscipline
  /\ NoDecrease
  /\ NoBigJumps

(*
  Liveness: eventual stabilization at MaxVal (i.e., 5)
*)
StabilizesAtMax ==
  <>[](c = MaxVal)

====================================================================================