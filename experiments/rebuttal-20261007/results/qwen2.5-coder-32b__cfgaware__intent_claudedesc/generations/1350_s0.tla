------------------------------- MODULE CounterSpec -------------------------------

CONSTANTS MaxValue

VARIABLES counter

(*--algorithm Counter
variables counter = 1;

begin
    while counter < MaxValue do
        await counter < MaxValue;
        counter := counter + 1;
    end while;
end algorithm;*)

Init == counter = 1

Next ==
    \/ /\ counter < MaxValue
       /\ counter' = counter + 1
    \/ /\ counter = MaxValue
       /\ counter' = counter

Spec ==
    Init /\ [][Next]_<<counter>>

WF == WF_next(<<counter>>)

Liveness ==
    <>[](counter = MaxValue) /\ [](counter = MaxValue => []<>(counter = MaxValue))

=============================================================================