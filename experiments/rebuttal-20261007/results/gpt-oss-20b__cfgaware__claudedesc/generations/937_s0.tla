------------------------------ MODULE LivenessHourClock ------------------------------
EXTENDS HourClock

(* ------------------------------------------------------------------
   The liveness specification extends the base hour‑clock with weak
   fairness on the tick action.
   ------------------------------------------------------------------ *)

LSpec == HC /\ WF_hr(HCnxt)

(* ------------------------------------------------------------------
   Temporal properties to be proved from LSpec.
   ------------------------------------------------------------------ *)

AlwaysTick      == [] <> HCnxt
AllTimes        == \A n \in 1..12 : [] <> (hr = n)
TypeInvariance  == [] HCini

THEOREM LivenessHourClock_Properties ==
  LSpec => (AlwaysTick /\ AllTimes /\ TypeInvariance)

=============================================================================