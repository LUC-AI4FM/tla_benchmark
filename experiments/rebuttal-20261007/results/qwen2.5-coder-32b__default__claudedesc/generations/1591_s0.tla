------------------------------- MODULE EvenOdd -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N \* Assumed to be fixed at 6 in the configuration

VARIABLES pc, result, stack, xEven, xOdd

Init == 
    /\ pc = "Start"
    /\ result = FALSE
    /\ stack = << >>
    /\ xEven = N
    /\ xOdd = N

Next ==
    \/ /\ pc = "Start"
       /\ UNCHANGED <<result, stack>>
       /\ xEven' = N
       /\ xOdd' = N
       /\ stack' = << >> 
       /\ pc' = "CallEven"
    \/ /\ pc = "CallEven"
       /\ xEven > 0
       /\ result' = FALSE
       /\ stack' = Append(stack, "Even")
       /\ xEven' = xEven - 1
       /\ xOdd' = xEven - 1
       /\ pc' = "CallOdd"
    \/ /\ pc = "CallEven"
       /\ xEven = 0
       /\ result' = TRUE
       /\ UNCHANGED <<stack, xEven, xOdd>>
       /\ pc' = "Done"
    \/ /\ pc = "CallOdd"
       /\ xOdd > 0
       /\ result' = FALSE
       /\ stack' = Append(stack, "Odd")
       /\ xEven' = xOdd - 1
       /\ xOdd' = xOdd - 1
       /\ pc' = "CallEven"
    \/ /\ pc = "CallOdd"
       /\ xOdd = 0
       /\ result' = FALSE
       /\ UNCHANGED <<stack, xEven>>
       /\ xOdd' = Head(Rev(stack))
       /\ stack' = Tail(Rev(stack))[1..Len(Tail(Rev(stack)))]
       /\ pc' = "Return"

Spec ==
    /\ Init
    /\ [][Next]_<<pc, result, stack, xEven, xOdd>>
    /\ WF_vars(<<pc, result, stack, xEven, xOdd>>)

Termination == 
    <>[](pc = "Done")

InOdd ==
    pc = "CallOdd"

CallOdd ==
    \/ pc = "Start"
    \/ pc = "CallEven"

PossibleCounts ==
    /\ _POSSIBLE(InOdd) = 3
    /\ _POSSIBLE(CallOdd) = 4

=============================================================================