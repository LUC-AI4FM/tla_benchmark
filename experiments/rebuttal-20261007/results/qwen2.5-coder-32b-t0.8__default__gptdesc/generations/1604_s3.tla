```tla
MODULE PlusCalToTLA

EXTENDS Integers, TLC, Sequences

CONSTANTS
    \* No constants are needed for this simple specification

VARIABLES
    pc,          \* Program counter
    localVars,   \* Local variables of the process
    stack        \* Stack of activation records

Init == 
    /\ pc = "start"
    /\ localVars = [proc |-> << >>]
    /\ stack = << >>

Next ==
    \/ /\ pc = "start"
       /\ localVars' = [localVars EXCEPT ![proc] = <<0, "">>]
       /\ stack' = stack
       /\ pc' = "addition"
    \/ /\ pc = "addition"
       /\ localVars' = [localVars EXCEPT ![proc][1] = localVars[proc][1] + 5]
       /\ stack' = Append(stack, <<pc, localVars[proc]>>)
       /\ pc' = "convertToString"
    \/ /\ pc = "convertToString"
       /\ LET result == Str(localVars[proc][1])
        IN /\ localVars' = [localVars EXCEPT ![proc][2] = result]
           /\ stack' = << >>  \* Clear the stack as we are done
           /\ pc' = "done"

Spec ==
    /\ Init
    /\ [][Next]_<<pc, localVars, stack>>
    /\ <><PCalled>>_<<pc, localVars, stack>>

\* Safety properties
SafetyInteger == 
    \/ pc # "convertToString"
    \/ localVars[proc][1] = 10

SafetyString ==
    \/ pc # "done"
    \/ localVars[proc][2] = "10"

\* Liveness properties
Termination == 
    <>[](pc = "done")

Fairness ==
    WF_<<pc, localVars, stack>>(PCalled)

Assertions ==
    /\ SafetyInteger
    /\ SafetyString

CompleteSpec ==
    Spec /\ Assertions /\ Fairness /\ Termination

====

```