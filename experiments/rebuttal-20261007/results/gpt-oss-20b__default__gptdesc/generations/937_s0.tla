MODULE AugmentedHourClock
EXTENDS HourClock

CONSTANTS Counterexample

(* Conjoin inherited clock specification with weak fairness on Next action *)
LSpec == Init /\ [][Next]_hr /\ WF_A(Next)

Spec == LSpec

TickInfinitely          == [](<> Next)
EachHourRecursInfinitely == \A h \in 1..12 : [](<> (hr = h))
TypeInvariantAlways    == [] (hr ∈ 1..12)

Postcondition == Counterexample

THEOREM LSpecImpliesProperties ==
  Spec => TickInfinitely /\ EachHourRecursInfinitely /\ TypeInvariantAlways /\ Postcondition