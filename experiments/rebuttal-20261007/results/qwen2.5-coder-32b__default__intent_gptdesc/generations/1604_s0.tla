------------------------------- MODULE SingleThreadedProgram -------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS ExpectedString

VARIABLES 
    stack,          \* The call stack
    output,         \* The global output string
    mainStep,       \* Current step in the main sequence (1 to 4)
    addResult,      \* Result of the addition procedure
    convertResult   \* Result of the conversion procedure

Init == 
    /\ stack = << >>
    /\ output = ""
    /\ mainStep = 1
    /\ addResult = 0
    /\ convertResult = ""

Next ==
    \/ /\ mainStep = 1
       /\ stack' = Append(stack, [returnLoc |-> 2, locals |-> []])
       /\ mainStep' = 3
       /\ UNCHANGED <<output, addResult, convertResult>>
    \/ /\ mainStep = 3
       /\ LET arg1 \in 5
          arg2 \in 7
          sum \in arg1 + arg2
       IN
           /\ stack' = Append(stack, [returnLoc |-> 4, locals |-> <<arg1, arg2>>])
           /\ addResult' = sum
           /\ mainStep' = 5
           /\ UNCHANGED <<output, convertResult>>
    \/ /\ mainStep = 5
       /\ LET frame \in Head(stack)
          args \in frame.locals
          expectedSum \in 12
       IN
           /\ addResult = expectedSum
           /\ stack' = Tail(stack)
           /\ mainStep' = frame.returnLoc
           /\ UNCHANGED <<output, convertResult>>
    \/ /\ mainStep = 4
       /\ stack' = Append(stack, [returnLoc |-> 6, locals |-> []])
       /\ mainStep' = 7
       /\ UNCHANGED <<output, addResult, convertResult>>
    \/ /\ mainStep = 7
       /\ LET arg \in addResult
          expectedArg \in 12
       IN
           /\ IF arg = expectedArg THEN convertResult' = ExpectedString ELSE convertResult' = "ERROR"
           /\ stack' = Tail(stack)
           /\ mainStep' = 8
           /\ UNCHANGED <<output, addResult>>
    \/ /\ mainStep = 6
       /\ output' = convertResult
       /\ mainStep' = 9
       /\ UNCHANGED <<stack, addResult, convertResult>>
    \/ /\ mainStep = 9
       /\ stack' = << >>
       /\ mainStep' = 10
       /\ UNCHANGED <<output, addResult, convertResult>>

Spec ==
    /\ Init
    /\ [][Next]_<<mainStep, stack, output, addResult, convertResult>>
    /\ WF_[Next]_<<mainStep, stack, output, addResult, convertResult>>

Termination ==
    <>(mainStep = 10)

Safety ==
    \/ mainStep # 10
    \/ output = ExpectedString

Liveness ==
    Termination

=============================================================================