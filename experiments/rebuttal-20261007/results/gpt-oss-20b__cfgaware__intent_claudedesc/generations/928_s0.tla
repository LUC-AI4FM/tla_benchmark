------------------------------ MODULE ClockEquivalence ------------------------------
EXTENDS HourClock

(* Primary next‑state relation: increment hour with wrap‑around at 12 *)
HC == [hour' = IF hour = 12 THEN 1 ELSE hour + 1]

(* Alternative next‑state relation using modular arithmetic *)
HC2 == [hour' = ((hour MOD 12) + 1)]

(* Initial condition: hour is a value in the range 1..12 *)
Init == hour \in 1..12

(* Specifications built from the shared initial condition *)
SpecPrimary    == Init /\ [][HC]_hour
SpecAlternative == Init /\ [][HC2]_hour

THEOREM Equivalence == SpecPrimary <=> SpecAlternative
=============================================================================