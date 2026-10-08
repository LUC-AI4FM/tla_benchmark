------------------------------- MODULE ProcComp -------------------------------
EXTENDS Integers, TLC, Sequences

CONSTANTS 
    \* No constants needed for this specification

VARIABLES 
    sumResult, strResult, output, state

Init == 
    /\ sumResult = 0
    /\ strResult = ""
    /\ output = ""
    /\ state = "start"

Next ==
    \/ /\ state = "start"
       /\ sumResult' = 3 + 7
       /\ UNCHANGED <<strResult, output>>
       /\ state' = "add_done"
    \/ /\ state = "add_done"
       /\ strResult' = IF sumResult = 10 THEN "10" ELSE ""
       /\ UNCHANGED <<sumResult, output>>
       /\ state' = "convert_done"
    \/ /\ state = "convert_done"
       /\ output' = strResult
       /\ ASSERT output = "10"
       /\ UNCHANGED <<sumResult, strResult>>
       /\ state' = "completed"

Spec == 
    Init /\ [][Next]_<<sumResult, strResult, output, state>> /\ <><Fair>[][state = "start"]_<<sumResult, strResult, output, state>>

Completed ==
    state = "completed"
    
=============================================================================