------------------------------ MODULE LivenessHourClock ------------------------------
EXTENDS TLA+, HourClock

(* --------------------------------------------------------------------------- *)
(*  Weak fairness operator specialized for the hour clock step action          *)
(* --------------------------------------------------------------------------- *)

WF_hr(a) == WF_Enabled(a)

(* --------------------------------------------------------------------------- *)
(*  Specification: combines the inherited hour‑clock spec with weak fairness   *)
(* --------------------------------------------------------------------------- *)

LSpec == HC /\ WF_hr(HCnxt)

(* --------------------------------------------------------------------------- *)
(*  Temporal properties to be proved from LSpec                               *)
(* --------------------------------------------------------------------------- *)

AlwaysTick    == [] <> HCnxt
AllTimes      == \A i \in 1..12 : [] <> (hr = i)
TypeInvariance== [] (hr \in 1..12)

(* --------------------------------------------------------------------------- *)
(*  Theorem: the properties hold under LSpec                                 *)
(* --------------------------------------------------------------------------- *)

THEOREM PropertiesFromLSpec ==
  LSpec => (AlwaysTick /\ AllTimes /\ TypeInvariance)

(* --------------------------------------------------------------------------- *)
(*  Counterexample to a settling property: no hour value can eventually stay *)
(*  forever.                                                                   *)
(* --------------------------------------------------------------------------- *)

THEOREM NoSettling ==
  LSpec => ~ (\E i \in 1..12 : <> [] (hr = i))

END LivenessHourClock