------------------------------- MODULE AugmentedHourClock -------------------------------
EXTENDS HourClock

CONSTANTS HC, HCnxt

VARIABLES hr

Init == HC!Init

Next == HC!Next

WF_hr_HCnxt == WF_vars(HCnxt, <<hr>>)

Spec ==
  /\ Init
  /\ [][Next]_<<hr>>
  /\ WF_hr_HCnxt

THEOREM Spec =>
  /\ []<>HCnxt
  /\ []<>(\E h \in 1..12: hr = h)
  /\ [](Init => HC!Init)

Postcondition ==
  <>(\A h \in 1..12: <>[](hr = h))

=============================================================================