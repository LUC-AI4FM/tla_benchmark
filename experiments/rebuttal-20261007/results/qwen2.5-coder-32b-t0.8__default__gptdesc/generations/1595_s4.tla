------------------------------- MODULE SequentialCounter -------------------------------

EXTENDS Integers, FiniteSets

CONSTANTS MaxCount

VARIABLES x, pc

(*--algorithm SequentialCounter
variables x = 0;
begin
    while x < MaxCount do
        await x < MaxCount;
        x := x + 1;
    end while;
    pc := "Done";
end algorithm*)

Init == /\ x = 0 
        /\ pc = "Start"

Next == \/ /\ pc = "Start"
               /\ x < MaxCount
               /\ x' = x + 1
               /\ pc' = "Start"
          \/ /\ pc = "Start"
               /\ x >= MaxCount
               /\ pc' = "Done"

Spec ==
    /\ Init
    /\ [][Next]_<<pc, x>>
    /\ WF_next(<<pc, x>>)

FinishLoop == pc = "Done"
AtFive == x = 5

PossibleCounts ==
    <>(/\ x \in 0..MaxCount
        /\ /\ [][Next]_<<pc, x>>
           /\ WF_next(<<pc, x>>))

=============================================================================