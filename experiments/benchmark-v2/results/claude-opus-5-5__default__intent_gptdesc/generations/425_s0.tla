---- MODULE NegativeCountdown ----
EXTENDS Integers

CONSTANTS Start, Cutoff

ASSUME StartAssumption  == Start \in Int /\ Start < 0
ASSUME CutoffAssumption == Cutoff \in Int /\ Cutoff <= Start

VARIABLES x

vars == <<x>>

Init == x = Start

Decrement ==
    /\ x > Cutoff
    /\ x' = x - 1

Done ==
    /\ x = Cutoff
    /\ UNCHANGED x

Next == Decrement \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Decrement)

TypeOK == x \in Int

AtMostInitial == x <= Start

AtLeastCutoff == x >= Cutoff

Bounds == x \in Cutoff..Start

Inv == TypeOK /\ AtMostInitial /\ AtLeastCutoff /\ Bounds

NeverIncreases == [][x' <= x]_vars

StepIsDecrementOrStutter == [][x' = x - 1]_vars

StaysAtCutoff == [](x = Cutoff => [](x = Cutoff))

FrozenAtCutoff == [][x = Cutoff => x' = Cutoff]_vars

EventuallyReachesCutoff == <>(x = Cutoff)

EventuallyAlwaysCutoff == <>[](x = Cutoff)

Liveness == EventuallyReachesCutoff /\ EventuallyAlwaysCutoff

SafetyOnlySpec == Init /\ [][Next]_vars

THEOREM Spec => []Inv
THEOREM Spec => NeverIncreases /\ StaysAtCutoff /\ FrozenAtCutoff
THEOREM Spec => Liveness
====