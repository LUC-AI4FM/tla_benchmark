MODULE AugmentedHourClock

EXTENDS HourClock, Temporal

(* Weak fairness of hour clock step *)
WF_HR == WF_Always(HCnxt)

LSpec == HC /\ WF_HR

TickInfinitelyOften == []<>(HCnxt)
Recurrence == \A n \in 1..12 : []<>(hr = n)
TypingInvariant == [] (hr \in 1..12)

THEOREM LSpecImpliesProps ==
  LSpec => TickInfinitelyOnce /\ Recurrence /\ TypingInvariant

(* Concrete counterexample structure for a settling property *)
CtrExample == [ hr' = 12, hr = 11 ]

=============================================================================