------------------------------- MODULE SequentialCounter -------------------------------

CONSTANTS MaxCount == 10

VARIABLES pc, x

(*--algorithm SequentialCounter
variables pc = "Start", x = 0;

fair do
    if
        /\ pc = "Start"
        /\ x < MaxCount
    then
        pc := "Increment";
        x := x + 1;
    else
        if
            /\ pc = "Increment"
            /\ x >= MaxCount
        then
            pc := "Done";
        end if;
    end if;
od;

end algorithm *)

Next == \/ /\ pc = "Start"
             /\ x < MaxCount
             /\ pc' = "Increment"
             /\ x' = x + 1
          \/ /\ pc = "Increment"
             /\ x >= MaxCount
             /\ pc' = "Done"
             /\ x' = x

Spec ==
    /\ PCInit
    /\ [][Next]_<<pc, x>>
    /\ WF_next(<<pc, x>>)

PCInit == /\ pc = "Start"
          /\ x = 0

Termination == <>[](pc = "Done")

AtFive == x = 5

FinishLoop == pc = "Done"

PossibleCounts ==
    /\ [][Next]_<<pc, x>>
    /\ <>(x \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9})
    /\ WF_next(<<pc, x>>)

=============================================================================