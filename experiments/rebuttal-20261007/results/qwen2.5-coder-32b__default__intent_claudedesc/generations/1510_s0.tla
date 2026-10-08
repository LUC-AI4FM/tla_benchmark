------------------------------- MODULE CaseExample -------------------------------
EXTENDS Integers, TLC

CONSTANTS 
    VALUES,  \* A finite set of integers
    TARGET_VALUE,  \* An integer in VALUES
    CONSTANT_VALUE  \* The constant value to assign

VARIABLES 
    chosen,  \* An integer from VALUES
    func  \* A function mapping VALUES to integers

Init == /\ chosen \in VALUES
        /\ func = [v \in VALUES |-> 0]

Next == \/ /\ chosen = TARGET_VALUE
             /\ func' = [func EXCEPT ![TARGET_VALUE] = CONSTANT_VALUE]
          \/ /\ chosen # TARGET_VALUE
             /\ func' = func

Spec == Init /\ [][Next]_<<chosen, func>>

================================================================================