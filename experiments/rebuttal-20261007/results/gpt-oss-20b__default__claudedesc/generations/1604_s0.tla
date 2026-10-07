MODULE PlusCalPlayground
EXTENDS Naturals, Sequences

VARIABLES retval, output, stack, step

Init == /\ retval = 0
        /\ output = ""
        /\ stack = <<>>
        /\ step = 0

AddProc ==
    /\ stack ≠ <<>>
    /\ Head(stack)[1] = "add"
    /\ LET a = Head(stack)[2]
           b = Head(stack)[3]
       IN  /\ retval' = a + b
            /\ stack' = Tail(stack)
            /\ UNCHANGED <<output, step>>

ToStringProc ==
    /\ stack ≠ <<>>
    /\ Head(stack)[1] = "to_string"
    /\ LET x = Head(stack)[2]
       IN  /\ x = 10
            /\ retval' = "10"
            /\ stack' = Tail(stack)
            /\ UNCHANGED <<output, step>>

MainStep0 ==
    /\ step = 0
    /\ stack = <<>>
    /\ stack' = Append(stack, ["add",3,7])
    /\ step' = 1
    /\ UNCHANGED <<retval, output>>

MainStep1 ==
    /\ step = 1
    /\ stack = <<>>
    /\ stack' = Append(stack, ["to_string", retval])
    /\ step' = 2
    /\ UNCHANGED <<retval, output>>

MainStep2 ==
    /\ step = 2
    /\ stack = <<>>
    /\ output' = retval
    /\ step' = 3
    /\ UNCHANGED <<retval, stack>>

MainStep3 ==
    /\ step = 3
    /\ stack = <<>>
    /\ output = "10"
    /\ step' = 4
    /\ UNCHANGED <<retval, stack>>

MainAction == MainStep0 \/ MainStep1 \/ MainStep2 \/ MainStep3

Next == AddProc \/ ToStringProc \/ MainAction

Termination == <> (step = 4)

Spec == Init /\ [][Next]_(<<retval, output, stack, step>>) 
        /\ WF(MainAction)
        /\ WF(AddProc)
        /\ WF(ToStringProc)
        /\ Termination
===============================================================================