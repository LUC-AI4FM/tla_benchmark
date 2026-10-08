---------------------------- MODULE ProcedureCallSpec ----------------------------

EXTENDS Integers, Sequences, TLC

CONSTANTS 
    \* No constants needed for this simple example

VARIABLES 
    pc,           \* Program counter for the main process
    localVars,     \* Local variables for each procedure call (stack of records)
    result         \* Final output string

Init == /\ pc = "start"
        /\ localVars = << >>
        /\ result = ""

Next == \/ \* Addition procedure
           (pc = "start" 
            /\ localVars' = Append(localVars, [arg1 |-> 5, arg2 |-> 5, retAddr |-> "convertToString"])
            /\ pc' = "add")
         \/ \* Perform addition
            (pc = "add"
            /\ LET top == Head(localVars)
               IN /\ localVars' = Append(Tail(localVars), [top EXCEPT !.result |-> (top.arg1 + top.arg2)])
                  /\ pc' = top.retAddr)
         \/ \* Convert to string procedure
            (pc = "convertToString"
            /\ LET top == Head(localVars)
               IN /\ result' = IntToString(top.result)
                  /\ localVars' = Tail(localVars)
                  /\ pc' = "done")
         \/ \* Termination state
            (pc = "done" 
            /\ UNCHANGED <<localVars, result>>)

Spec == Init /\ [][Next]_<<pc, localVars, result>>

\* Safety invariants
Safety ==
    /\ \A i \in 1..Len(localVars) : localVars[i].result' = localVars[i].arg1 + localVars[i].arg2
    /\ pc = "done" => result = IntToString(10)

\* Liveness properties
Termination == <>[](pc = "done")

Progress ==
    /\ WF_[Next]_<<pc, localVars, result>>
    /\ SF_<>(pc = "convertToString")

Invariant == Init /\ [][Next]_<<pc, localVars, result>> /\ <<Safety>>

THEOREM Spec => []Invariant

\* Fairness conditions
FairSpec == Spec /\ Progress

=============================================================================