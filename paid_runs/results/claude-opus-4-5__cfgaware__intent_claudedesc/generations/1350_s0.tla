---------------------------- MODULE spec ----------------------------

VARIABLE counter

Init == counter = 1

Increment == 
    /\ counter < 5
    /\ counter' = counter + 1

Stutter ==
    /\ counter = 5
    /\ counter' = counter

Next == Increment \/ Stutter

Spec == Init /\ [][Next]_counter /\ WF_counter(Increment)

StableAt5 == [](counter = 5 => [](counter = 5))

Liveness == (counter = 1) ~> (counter = 5 /\ [](counter = 5))

=================================================================