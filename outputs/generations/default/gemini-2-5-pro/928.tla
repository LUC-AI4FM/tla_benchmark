---- MODULE HC2 ----
EXTENDS HourClock, Integers

\* An alternative next-state action for the hour clock.
HCnxt2 == hr' = (hr % 12) + 1

\* The complete specification using the alternative next-state action.
HC2 == HCini /\ [][HCnxt2]_hr

\* The theorem asserting that the new specification is equivalent to the original one.
THEOREM HC <=> HC2

====================