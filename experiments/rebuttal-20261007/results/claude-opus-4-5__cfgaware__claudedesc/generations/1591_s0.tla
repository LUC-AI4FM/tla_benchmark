---------------------------- MODULE EvenOdd ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT N

VARIABLES pc, result, stack, xEven, xOdd

vars == <<pc, result, stack, xEven, xOdd>>

Init ==
    /\ pc = "Main"
    /\ result = FALSE
    /\ stack = <<>>
    /\ xEven = 0
    /\ xOdd = 0

CallEven(n) ==
    /\ pc = "Main"
    /\ xEven' = n
    /\ stack' = Append(stack, <<"Main", xEven, xOdd>>)
    /\ pc' = "Even"
    /\ UNCHANGED <<result, xOdd>>

EvenBase ==
    /\ pc = "Even"
    /\ xEven = 0
    /\ result' = TRUE
    /\ IF stack /= <<>>
       THEN /\ pc' = Head(stack)[1]
            /\ xEven' = Head(stack)[2]
            /\ xOdd' = Head(stack)[3]
            /\ stack' = Tail(stack)
       ELSE /\ pc' = "Print"
            /\ UNCHANGED <<stack, xEven, xOdd>>

EvenRecurse ==
    /\ pc = "Even"
    /\ xEven > 0
    /\ xOdd' = xEven - 1
    /\ stack' = Append(stack, <<"EvenReturn", xEven, xOdd>>)
    /\ pc' = "Odd"
    /\ UNCHANGED <<result, xEven>>

EvenReturn ==
    /\ pc = "EvenReturn"
    /\ IF stack /= <<>>
       THEN /\ pc' = Head(stack)[1]
            /\ xEven' = Head(stack)[2]
            /\ xOdd' = Head(stack)[3]
            /\ stack' = Tail(stack)
       ELSE /\ pc' = "Print"
            /\ UNCHANGED <<stack, xEven, xOdd>>
    /\ UNCHANGED result

OddBase ==
    /\ pc = "Odd"
    /\ xOdd = 0
    /\ result' = FALSE
    /\ IF stack /= <<>>
       THEN /\ pc' = Head(stack)[1]
            /\ xEven' = Head(stack)[2]
            /\ xOdd' = Head(stack)[3]
            /\ stack' = Tail(stack)
       ELSE /\ pc' = "Print"
            /\ UNCHANGED <<stack, xEven, xOdd>>

OddRecurse ==
    /\ pc = "Odd"
    /\ xOdd > 0
    /\ xEven' = xOdd - 1
    /\ stack' = Append(stack, <<"OddReturn", xEven, xOdd>>)
    /\ pc' = "Even"
    /\ UNCHANGED <<result, xOdd>>

OddReturn ==
    /\ pc = "OddReturn"
    /\ IF stack /= <<>>
       THEN /\ pc' = Head(stack)[1]
            /\ xEven' = Head(stack)[2]
            /\ xOdd' = Head(stack)[3]
            /\ stack' = Tail(stack)
       ELSE /\ pc' = "Print"
            /\ UNCHANGED <<stack, xEven, xOdd>>
    /\ UNCHANGED result

Print ==
    /\ pc = "Print"
    /\ PrintT(result)
    /\ pc' = "Done"
    /\ UNCHANGED <<result, stack, xEven, xOdd>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ CallEven(N)
    \/ EvenBase
    \/ EvenRecurse
    \/ EvenReturn
    \/ OddBase
    \/ OddRecurse
    \/ OddReturn
    \/ Print
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

InOdd == pc = "Odd"

CallOdd == pc = "Odd" /\ xOdd > 0

PossibleCounts == TRUE

==========================================================================