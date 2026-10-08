---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

\* Valid hour values on a 12-hour dial
Hours == 1..12

\* Initial state: any valid hour
Init == hr \in Hours

\* Stepwise "increment-or-wrap" transition description
Next1 == IF hr = 12 THEN hr' = 1 ELSE hr' = hr + 1

\* Alternative concise transition using modular arithmetic
\* Computes next hour as: ((hr - 1) + 1) mod 12 + 1 = hr mod 12 + 1
Next2 == hr' = (hr % 12) + 1

\* The main next-state relation (using increment-or-wrap formulation)
Next == Next1

\* Safety invariant: hour is always a valid value in 1..12
TypeInvariant == hr \in Hours

\* The specification with fairness for liveness
Spec == Init /\ [][Next]_hr /\ WF_hr(Next)

\* Alternative specification using modular arithmetic formulation
Spec2 == Init /\ [][Next2]_hr /\ WF_hr(Next2)

\* Equivalence property: both transition formulations produce the same result
TransitionEquivalence == (Next1 <=> Next2)

\* Invariant that the two formulations are equivalent in every state
EquivalenceInvariant == (ENABLED Next1) = (ENABLED Next2)

\* Liveness: the clock always eventually advances (makes progress)
Progress == []<><<Next>>_hr

\* Liveness: every hour is visited infinitely often
\* The clock eventually visits hour 1, hour 2, ..., hour 12
VisitsAll == \A h \in Hours : []<>(hr = h)

\* Safety property: we never leave the valid range
AlwaysValid == [](hr \in Hours)

\* HC: The main hour clock specification
HC == Spec

\* HC2: The alternative specification using modular arithmetic
HC2 == Spec2

==========================================================================