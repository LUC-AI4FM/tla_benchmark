MODULE HourClockLiveness
EXTENDS HourClock, Temporal

CONSTANTS \* none

(* Liveness specification augmenting HourClock with weak fairness on the clock step *)
LSpec == HourClock.Spec ∧ WF_A(HCNext)

(* Temporal properties *)
TickInfinitelyOften == []<>(HCNext)
EveryHourRecurs == ∀ v ∈ {1..12} : []<>(hr = v)
InvariantTyping == [] (hr ∈ 1..12)

Spec == LSpec

THEOREM TicksForever: Spec => TickInfinitelyOften
THEOREM EveryHourRecursForever: Spec => EveryHourRecurs
THEOREM TypingInvariant: Spec => InvariantTyping

(* Counterexample for settling property *)
SettlingProperty == <> (hr = 1) ∧ [](hr = 1)
THEOREM NoSettlingUnderLSpec: Spec => ~SettlingProperty

===============================================================================