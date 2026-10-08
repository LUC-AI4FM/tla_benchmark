----------------------------- MODULE AugmentedHourClock -----------------------------
EXTENDS HourClock

(* No new CONSTANTS or VARIABLES *)

Init == TRUE

Next == HCnxt

Spec == Init /\ [][Next]_{hr} /\ WF_HCnxt

LSpec == Spec

TickInfinitelyOften == []<>(HCnxt)

AllHoursRecurr ==
    \A h \in 1..12 : []<>(hr = h)

TypingInvariant == [] (hr \in 1..12)

THEOREM SpecImpliesProperties ==
    LSpec => TickInfinitelyOften /\ AllHoursRecurr /\ TypingInvariant

PostCondition ==
   /\ hr = 1
   /\ [] (hr = 1)

END MODULE