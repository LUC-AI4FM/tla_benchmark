MODULE ClockWithLiveness
EXTENDS HourClock

VARIABLES hr

(* Conjoin the inherited clock specification HC with weak fairness on HCnxt *)
LSpec == HC /\ WF_hr(HCnxt)

(* Temporal properties *)
RecurringHours ==
  \A h \in 1..12 : []<>(hr = h)

Typing == hr \in 1..12

SettlingProperty == [] (hr = 12)

THEOREM PropsFromLSpec == LSpec
           => ([]<> HCnxt /\ RecurringHours /\ [] Typing)

THEOREM CounterexamplePost ==
  \E hr0 \in 1..12 : (hr = hr0) /\ ~SettlingProperty

(* End of module *)