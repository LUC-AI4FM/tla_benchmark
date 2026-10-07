------------------------------- MODULE Playground -------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS 
    \* No constants needed for this simple example

VARIABLES 
    retval,
    output,
    stack,
    pc

Init == 
    /\ retval = 0
    /\ output = ""
    /\ stack = << >>
    /\ pc = "start"

Next ==
    \/ /\ pc = "start"
       /\ UNCHANGED <<retval, output>>
       /\ stack' = <<1>>
       /\ pc' = "call_add"
    \/ /\ pc = "call_add"
       /\ retval' = 3 + 7
       /\ UNCHANGED <<output, stack>>
       /\ pc' = "return_from_add"
    \/ /\ pc = "return_from_add"
       /\ stack' = Tail(stack)
       /\ pc' = "call_to_string"
    \/ /\ pc = "call_to_string"
       /\ ASSERT retval = 10
       /\ UNCHANGED <<output>>
       /\ stack' = <<2, Head(stack)>>
       /\ pc' = "return_from_to_string"
    \/ /\ pc = "return_from_to_string"
       /\ retval' = "10"
       /\ stack' = Tail(stack)
       /\ pc' = "copy_retval_to_output"
    \/ /\ pc = "copy_retval_to_output"
       /\ output' = retval
       /\ UNCHANGED <<stack>>
       /\ pc' = "assert_final_value"
    \/ /\ pc = "assert_final_value"
       /\ ASSERT output = "10"
       /\ stack' = Tail(stack)
       /\ pc' = "Done"

Spec == 
    Init /\ [][Next]_<<retval, output, stack, pc>> /\ WF_<<pc>>[Next]

Termination ==
    <>(pc = "Done")

Liveness ==
    Termination

===============================================================================