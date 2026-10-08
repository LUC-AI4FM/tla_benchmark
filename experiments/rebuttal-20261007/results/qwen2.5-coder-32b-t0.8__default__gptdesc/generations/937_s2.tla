------------------------------ MODULE AugmentedHourClock ------------------------------

EXTENDS HourClock

CONSTANTS HC, HCnxt

VARIABLES hr

Init == HC!Init

Next == HC!Next

WF_hr_HCnxt == WF_hr(HCnxt)

Spec ==
  /\ Init
  /\ [][HCnxt]_<<hr>>
  /\ WF_hr_HCnxt

LivenessProperties ==
  /\ []<>HCnxt
  /\ [](HC!hc_values) ~> []<>(/\ HC!hc_value = 1 \/ HC!hc_value = 2 \/ HC!hc_value = 3 \/ HC!hc_value = 4 \/ HC!hc_value = 5 \/ HC!hc_value = 6 \/ HC!hc_value = 7 \/ HC!hc_value = 8 \/ HC!hc_value = 9 \/ HC!hc_value = 10 \/ HC!hc_value = 11 \/ HC!hc_value = 12)
  /\ []HC!Init

LSpec == Spec /\ LivenessProperties

THEOREM LSpec => LivenessProperties

=============================================================================