---------------------------- MODULE EvenOdd ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT N

ASSUME N \in Nat

VARIABLES pc, stack, xEven, xOdd, result

vars == <<pc, stack, xEven, xOdd, result>>

Init ==
    /\ pc = "Start"
    /\ stack = <<>>
    /\ xEven = 0
    /\ xOdd = 0
    /\ result = FALSE

Start ==
    /\ pc = "Start"
    /\ stack' = <<[caller |-> "Start", var |-> N]>>
    /\ xEven' = N
    /\ pc' = "EvenCheck"
    /\ UNCHANGED <<xOdd, result>>

EvenCheck ==
    /\ pc = "EvenCheck"
    /\ IF xEven = 0
       THEN /\ result' = TRUE
            /\ IF Len(stack) = 1
               THEN /\ pc' = "Done"
                    /\ stack' = <<>>
                    /\ UNCHANGED <<xEven, xOdd>>
               ELSE /\ LET frame == Head(Tail(stack))
                    IN IF frame.caller = "Even"
                       THEN /\ pc' = "EvenReturn"
                            /\ stack' = Tail(stack)
                            /\ UNCHANGED <<xEven, xOdd>>
                       ELSE /\ pc' = "OddReturn"
                            /\ stack' = Tail(stack)
                            /\ UNCHANGED <<xEven, xOdd>>
       ELSE /\ xOdd' = xEven - 1
            /\ stack' = Append(stack, [caller |-> "Even", var |-> xEven])
            /\ pc' = "OddCheck"
            /\ UNCHANGED <<xEven, result>>

OddCheck ==
    /\ pc = "OddCheck"
    /\ IF xOdd = 0
       THEN /\ result' = FALSE
            /\ IF Len(stack) = 1
               THEN /\ pc' = "Done"
                    /\ stack' = <<>>
                    /\ UNCHANGED <<xEven, xOdd>>
               ELSE /\ LET frame == Head(Tail(stack))
                    IN IF frame.caller = "Even"
                       THEN /\ pc' = "EvenReturn"
                            /\ stack' = Tail(stack)
                            /\ UNCHANGED <<xEven, xOdd>>
                       ELSE /\ pc' = "OddReturn"
                            /\ stack' = Tail(stack)
                            /\ UNCHANGED <<xEven, xOdd>>
       ELSE /\ xEven' = xOdd - 1
            /\ stack' = Append(stack, [caller |-> "Odd", var |-> xOdd])
            /\ pc' = "EvenCheck"
            /\ UNCHANGED <<xOdd, result>>

EvenReturn ==
    /\ pc = "EvenReturn"
    /\ IF Len(stack) = 0
       THEN /\ pc' = "Done"
            /\ UNCHANGED <<stack, xEven, xOdd, result>>
       ELSE /\ LET frame == Head(stack)
            IN IF frame.caller = "Start"
               THEN /\ pc' = "Done"
                    /\ stack' = Tail(stack)
                    /\ UNCHANGED <<xEven, xOdd, result>>
               ELSE IF frame.caller = "Even"
                    THEN /\ pc' = "EvenReturn"
                         /\ stack' = Tail(stack)
                         /\ UNCHANGED <<xEven, xOdd, result>>
                    ELSE /\ pc' = "OddReturn"
                         /\ stack' = Tail(stack)
                         /\ UNCHANGED <<xEven, xOdd, result>>

OddReturn ==
    /\ pc = "OddReturn"
    /\ IF Len(stack) = 0
       THEN /\ pc' = "Done"
            /\ UNCHANGED <<stack, xEven, xOdd, result>>
       ELSE /\ LET frame == Head(stack)
            IN IF frame.caller = "Start"
               THEN /\ pc' = "Done"
                    /\ stack' = Tail(stack)
                    /\ UNCHANGED <<xEven, xOdd, result>>
               ELSE IF frame.caller = "Even"
                    THEN /\ pc' = "EvenReturn"
                         /\ stack' = Tail(stack)
                         /\ UNCHANGED <<xEven, xOdd, result>>
                    ELSE /\ pc' = "OddReturn"
                         /\ stack' = Tail(stack)
                         /\ UNCHANGED <<xEven, xOdd, result>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Start
    \/ EvenCheck
    \/ OddCheck
    \/ EvenReturn
    \/ OddReturn
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

=============================================================================