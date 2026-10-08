------------------------------- MODULE TrivialSystem -------------------------------

CONSTANTS x, y

VARIABLES state

(*--algorithm trivial_system
variables x = 0, y = 0;
begin
    Init:
        assert \A s \in {<<x,y>>}: s[1] = 0 /\ s[2] = 0 /\ s[2] = s[1];
    next ==
        /\ UNCHANGED <<x, y>>
end algorithm;*)

Init == \/ state = <<0, 0>>

Next == UNCHANGED <<x, y>>

Spec == Init /\ []Next

=============================================================================