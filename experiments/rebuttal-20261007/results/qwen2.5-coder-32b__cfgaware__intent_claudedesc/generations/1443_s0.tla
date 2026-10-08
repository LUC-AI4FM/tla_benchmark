------------------------------- MODULE CounterSpec -------------------------------

CONSTANTS
    \* No additional constants needed for this specification

VARIABLES
    counter

(* --algorithm Counter
variables counter = 0;

next == /\ counter' = (counter + 1) % 3

begin
    while TRUE do
        await next;
        counter := counter';
    end while;
end algorithm *)

Spec ==
    /\ counter \in {0, 1, 2}
    /\ [][next]_<<counter>>

Init == counter = 0

next == counter' = (counter + 1) % 3

\* Predicates of interest
ReachedTwo == counter = 2
EqualsOne == counter = 1
WrapAround == \/ counter = 2 /\ counter' = 0

=============================================================================