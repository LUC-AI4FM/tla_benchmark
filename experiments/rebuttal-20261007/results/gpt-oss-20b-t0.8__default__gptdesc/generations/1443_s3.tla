MODULE SimpleSM
EXTENDS Naturals

VARIABLES x

(* Initial state *)
Init == x = 0

(* State transition: advance modulo 3 *)
Next == x' = (x + 1) % 3

\* @named IsOne
IsOne == x = 1

\* @named Done
Done == x = 2

\* @named Wrapped
Wrapped == x = 0

(* Temporal specification with stuttering *)
Spec == Init /\ []_{x} (Next \/ x' = x)

(* TLC-specific coverage check *)
THEOREM CoverageCheck ==
  (TLCGet("IsOne") = 1) /\ (TLCGet("Done") = 1) /\ (TLCGet("Wrapped") = 1)