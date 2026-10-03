------------------------------- MODULE TrivialSystem -------------------------------

CONSTANTS x, y

VARIABLES state

Init == state = <<0, 0>>

Next == /\ state' = state

Spec == Init /\ [][Next]_<<x, y>>

THEOREM Spec => [](state = <<0, 0>>)

=============================================================================