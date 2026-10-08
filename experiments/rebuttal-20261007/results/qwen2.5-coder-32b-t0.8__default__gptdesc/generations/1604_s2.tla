---- MODULE ProcCallSpec ----
EXTENDS Integers, Sequences, TLC

CONSTANTS 
    \* No constants needed for this simple example

VARIABLES 
    pc,             \* Program counter
    result,         \* Result of addition
    outputString,   \* Final output string
    stack           \* Stack of activation records

Init == 
    /\ pc = "start"
    /\ result = 0
    /\ outputString = ""
    /\ stack = << >>

Next ==
    \/ /\ pc = "start"
       /\ result' = result + 5
       /\ pc' = "convertToString"
       /\ stack' = Append(stack, "additionReturn")
    \/ /\ pc = "convertToString"
       /\ result' = result
       /\ outputString' = STRING(result)
       /\ pc' = "end"
       /\ stack' = Tail(stack)
    \/ /\ pc = "end"
       /\ UNCHANGED <<result, outputString, stack>>
       /\ pc' = pc

Spec ==
    /\ Init
    /\ [][Next]_<<pc, result, outputString, stack>>

\* Safety invariants
Safety == 
    /\ \/ pc \in {"start", "convertToString", "end"}
    /\ \/ pc = "end" => outputString = "10"
       \/ pc # "end" => outputString = ""

\* Liveness properties
Termination ==
    <>[](pc = "end")

Fairness ==
    WF_next(<<pc, result, outputString, stack>>, Next)

CompleteSpec == 
    /\ Spec
    /\ Safety
    /\ Termination
    /\ Fairness

====