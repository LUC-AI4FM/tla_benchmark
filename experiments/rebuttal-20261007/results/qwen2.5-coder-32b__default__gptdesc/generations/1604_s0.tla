------------------------------- MODULE PlusCalProgram -------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS 
    \* No constants needed for this simple example

VARIABLES 
    pc,           \* Program counter
    localVars,    \* Local variables as a function of process and variable name
    stack         \* Stack of activation records

Init == 
    /\ pc = "start"
    /\ localVars = [<< >> \in {} |-> 0]
    /\ stack = << >>

Next ==
    \/ /\ pc = "start"
       /\ localVars[<< >>]["x"] = 5
       /\ localVars[<< >>]["y"] = 5
       /\ pc' = "add"
    \/ /\ pc = "add"
       /\ localVars[<< >>]["result"] = localVars[<< >>]["x"] + localVars[<< >>]["y"]
       /\ stack' = Append(stack, << "convertToString", localVars[<< >>] >>)
       /\ pc' = "convertToString"
    \/ /\ pc = "convertToString"
       /\ LET top == Head(stack) IN
          /\ ASSERT top[2]["result"] = 10
          /\ localVars[<< >>]["outputString"] = STRING(top[2]["result"])
          /\ stack' = Tail(stack)
          /\ pc' = "done"
    \/ /\ pc = "done"
       /\ ASSERT localVars[<< >>]["outputString"] = "10"
       /\ pc' = "done"

Spec == 
    Init /\ [][Next]_<<pc, localVars, stack>> /\ WF_next(<<pc, localVars, stack>>, Next)

WF_next(vars, action) ==
    \A s \in StateSpace: action[s] => vars' \in StateSpace

StateSpace ==
    {s \in [pc : {"start", "add", "convertToString", "done"},
             localVars : [<< >> \in {} |-> Int],
             stack : Seq(<< _, _ >>)] :
        /\ (pc = "start" => localVars[<< >>]["x"] = 5 /\ localVars[<< >>]["y"] = 5)
        /\ (pc = "add" => localVars[<< >>]["result"] = localVars[<< >>]["x"] + localVars[<< >>]["y"])
        /\ (pc = "convertToString" => Len(stack) > 0)
        /\ (pc = "done" => localVars[<< >>]["outputString"] = "10")}

Termination ==
    <>[](pc = "done")

Progress ==
    WF_next(<<pc, localVars, stack>>, Next)

=============================================================================