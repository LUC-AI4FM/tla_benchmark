------------------------------- MODULE ProgramModel -------------------------------

CONSTANTS
    \* Constants to be defined by the model checker
    defaultInitValue

VARIABLES
    stack,  \* The call stack
    output, \* The global output string
    pc      \* The program counter indicating the current step in main

\* Initial state: empty stack, no output, and starting at the first step of main
Init == 
    /\ stack = << >>
    /\ output = ""
    /\ pc = 1

\* Actions for the main sequence of steps
MainStep1 ==
    \* Invoke the add procedure with arguments 3 and 5
    /\ pc = 1
    /\ stack' = Append(stack, [returnPc \ 2, locals \ << >>])
    /\ UNCHANGED output
    /\ pc' = "add"

MainStep2 ==
    \* Pass the result of add to intToString procedure
    /\ pc = 2
    /\ LET result = Head(stack).locals[1] IN
        /\ stack' = Append(stack, [returnPc \ 3, locals \ <<result>>])
        /\ UNCHANGED output
        /\ pc' = "intToString"

MainStep3 ==
    \* Record the returned string into global output
    /\ pc = 3
    /\ LET resultString = Head(stack).locals[1] IN
        /\ stack' = Tail(stack)
        /\ output' = resultString
        /\ pc' = "Done"
    
\* Actions for the add procedure
Add ==
    \* Compute the sum of two arguments and return to caller
    /\ pc = "add"
    /\ LET arg1 = 3
       arg2 = 5
       sum = arg1 + arg2 IN
        /\ stack' = Append(stack, [returnPc \ Head(stack).returnPc, locals \ <<sum>>])
        /\ UNCHANGED output
        /\ pc' = Head(stack).returnPc

\* Actions for the intToString procedure
IntToString ==
    \* Convert a specific integer to string and return to caller
    /\ pc = "intToString"
    /\ LET arg = Head(stack).locals[1] IN
        /\ IF arg = 8 THEN
            stack' = Append(stack, [returnPc \ Head(stack).returnPc, locals \ <<"8">>])
           ELSE
            stack' = Append(stack, [returnPc \ Head(stack).returnPc, locals \ <<>>])
        /\ UNCHANGED output
        /\ pc' = Head(stack).returnPc

\* Next state relation
Next ==
    \/ MainStep1
    \/ MainStep2
    \/ MainStep3
    \/ Add
    \/ IntToString

\* Specification of the system behavior
Spec == 
    Init /\ [][Next]_<<stack, output, pc>> /\ WF_[Next]_<<stack, output, pc>>

\* Termination condition: program reaches "Done" state and stack is empty
Termination ==
    \E s \in StateSpace : s.pc = "Done" /\ s.stack = << >>

\* Safety property: final output equals the expected string "8"
Safety ==
    \A s \in StateSpace : s.pc = "Done" => s.output = "8"

\* Liveness property: program eventually terminates
Liveness ==
    <>[](pc = "Done")

=============================================================================