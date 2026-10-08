---- MODULE CounterFactorial ----
EXTENDS Naturals

(*
  A simple counter system with two atomic update kinds:
  - Short update sets the counter to 3!
  - Long update sets the counter to 9!
  The initial counter is 0.
  Each step performs exactly one of the two updates.
*)

VARIABLE counter

RECURSIVE Fact(_)
Fact(n) == IF n = 0 THEN 1 ELSE n * Fact(n - 1)

ShortInput == 3
LongInput  == 9

ShortVal == Fact(ShortInput)
LongVal  == Fact(LongInput)

AllowedValues == {ShortVal, LongVal}

Init == counter = 0

Short == counter' = ShortVal
Long  == counter' = LongVal

(*
  Transition relation: at each step, exactly one of the updates occurs.
*)
Next == Short \/ Long

(*
  Overall behavior: start from Init and always take a permitted transition.
*)
Spec == Init /\ [] Next

(*
  Safety properties:
  - The counter is always either the initial 0 or one of the two factorial results.
  - Every transition assigns exactly one of the two factorial results.
*)
StateSafety == [] (counter = 0 \/ counter \in AllowedValues)
TransitionSafety == [] (Next => counter' \in AllowedValues)

(*
  Liveness expectations (stated as properties of the transition structure):
  - No deadlock: there is always some enabled transition.
  - Either kind of update may be chosen at every step (both are perpetually enabled).
*)
NoDeadlock == [] Enabled(Next)
EitherUpdateAlwaysEnabled == [] (Enabled(Short) /\ Enabled(Long))

====