---------------------------- MODULE SimpleCounter ----------------------------
EXTENDS Naturals

VARIABLES counter

Init == counter = 1

Increment == 
    /\ counter < 5
    /\ counter' = counter + 1

Stutter ==
    /\ counter = 5
    /\ UNCHANGED counter

Next == Increment \/ Stutter

Spec == Init /\ [][Next]_counter /\ WF_counter(Increment)

TypeInvariant == counter \in 1..5

SafetyInvariant == counter >= 1 /\ counter <= 5

StableAt5 == [](counter = 5 => [](counter = 5))

EventuallyReaches5 == <>(counter = 5)

LeadsToStable == (counter = 1) ~> [](counter = 5)

=============================================================================