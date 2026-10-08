MODULE TwoWorkers
EXTENDS Naturals, TLC

VARIABLES counter, ready1, ready2

Init ==
    counter = 0 /\
    ready1 = TRUE /\ ready2 = TRUE

Increment1 ==
    ready1 /\ 
    counter' = counter + 1 /\ 
    ready1' = FALSE /\ 
    ready2' = ready2

Increment2 ==
    ready2 /\ 
    counter' = counter + 1 /\ 
    ready2' = FALSE /\ 
    ready1' = ready1

Idle ==
    counter' = counter /\ 
    ready1' = ready1 /\ 
    ready2' = ready2

Next == Increment1 \/ Increment2 \/ Idle

vars == <<counter, ready1, ready2>>

Spec == Init /\ [][Next]_vars /\ WF_Enabled(Increment1) /\ WF_Enabled(Increment2)

SafetyInvariants ==
    counter \in Nat /\
    counter <= 2 /\
    (ready1 = FALSE /\ ready2 = FALSE) => counter = 2

THEOREM Safety == []SafetyInvariants
THEOREM Termination == <> (ready1 = FALSE /\ ready2 = FALSE)