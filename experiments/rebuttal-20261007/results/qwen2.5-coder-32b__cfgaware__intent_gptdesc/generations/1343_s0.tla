------------------------------- MODULE SimpleConcurrentSystem -------------------------------

CONSTANTS 
    \* No additional constants are needed for this specification

VARIABLES 
    loc1, 
    loc2

(*--algorithm SimpleConcurrentSystem
variables loc1 = 0, loc2 = 0;

begin
    while TRUE do
        await TRUE;
    end while;
end algorithm*)

Init == /\ loc1 = 0
        /\ loc2 = 0
        /\ loc1 = loc2

Next == \/ /\ loc1' = loc1
            /\ loc2' = loc2

Spec == Init /\ [][Next]_<<loc1, loc2>>

TypeOK == /\ loc1 \in Int
           /\ loc2 \in Int

Inv1 == loc1 = loc2

Inv2 == [](loc1 = loc2)

InitTemporalProperty == <>(Init)

StableValues == [](loc1' = loc1 /\ loc2' = loc2)

THEOREM Spec => []TypeOK
THEOREM Spec => InitTemporalProperty
THEOREM Spec => Inv1
THEOREM Spec => Inv2
THEOREM Spec => StableValues

=============================================================================