------------------------------- MODULE FischerMutex -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, Delta, Epsilon

VARIABLES x, timers, inCS

Init == /\ x = 0
        /\ timers = <<0>> \o [1..N -> 0]
        /\ inCS = {}

Next ==
    \/ \/ \E i \in 1..N : 
            (/\ timers[i] > 0
             /\ timers' = [timers EXCEPT ![i] = timers[i] - 1]
             /\ UNCHANGED <<x, inCS>>)
       \/ \/ \E i \in 1..N :
                (/\ x = 0
                 /\ timers[i] = 0
                 /\ timers' = [timers EXCEPT ![i] = Delta]
                 /\ x' = i
                 /\ UNCHANGED <<inCS>>)
           \/ \/ \E i \in 1..N :
                    (/\ x = i
                     /\ timers[i] > 0
                     /\ timers' = [timers EXCEPT ![i] = timers[i] - 1]
                     /\ UNCHANGED <<x, inCS>>)
               \/ \/ \E i \in 1..N :
                        (/\ x = i
                         /\ timers[i] = 0
                         /\ timers' = [timers EXCEPT ![i] = Epsilon]
                         /\ UNCHANGED <<x, inCS>>)
                   \/ \/ \E i \in 1..N :
                            (/\ x = i
                             /\ timers[i] = 0
                             /\ timers' = [timers EXCEPT ![i] = 0]
                             /\ x' = 0
                             /\ inCS' = {i}
                             /\ UNCHANGED <<>>)
                       \/ \/ \E i \in 1..N :
                                (/\ timers[i] > 0
                                 /\ timers' = [timers EXCEPT ![i] = timers[i] - 1]
                                 /\ UNCHANGED <<x, inCS>>)
                           \/ \/ \A i \in 1..N : timers[i] = 0
                                    /\ timers' = [timers EXCEPT ![\i \in 1..N] = 0]
                                    /\ UNCHANGED <<x, inCS>>

Spec ==
    /\ Init
    /\ [][Next]_<<x, timers, inCS>>
    /\ WF_<<x, timers, inCS>>[Next]

Invariant == \/ Cardinality(inCS) <= 1

Liveness == <>[](\E i \in 1..N : <>(i \in inCS))

SomeInCS ==
    LET SomeProcessInCS == (\E i \in 1..N : i \in inCS)
    IN
        [](SomeProcessInCS)

ClaimLock ==
    LET ProcessClaimsLock(i) == (/\ timers[i] = Delta \/ timers[i] = Epsilon)
    IN
        []<>(\E i \in 1..N : ProcessClaimsLock(i))

InvariantAssumption == Delta < Epsilon

THEOREM Spec => []Invariant

THEOREM Spec /\ InvariantAssumption => Liveness

CONFIGURATION <|
    N |-> 3,
    Delta |-> 2,
    Epsilon |-> 3
|>

=============================================================================