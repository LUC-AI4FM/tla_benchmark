---------------------------- MODULE EvenOdd ----------------------------
EXTENDS Naturals, Sequences, TLC

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

CallEven(x) ==
    /\ pc = "Start"
    /\ xEven' = x
    /\ stack' = Append(stack, [proc |-> "main", retpc |-> "Done"])
    /\ pc' = "EvenBody"
    /\ UNCHANGED <<xOdd, result>>

EvenBody ==
    /\ pc = "EvenBody"
    /\ IF xEven = 0
       THEN
           /\ result' = TRUE
           /\ pc' = "EvenReturn"
           /\ UNCHANGED <<stack, xEven, xOdd>>
       ELSE
           /\ stack' = Append(stack, [proc |-> "Even", retpc |-> "EvenReturn", savedXEven |-> xEven])
           /\ xOdd' = xEven - 1
           /\ pc' = "OddBody"
           /\ UNCHANGED <<xEven, result>>

EvenReturn ==
    /\ pc = "EvenReturn"
    /\ stack # <<>>
    /\ LET frame == Head(Reverse(stack))
       IN
           /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
           /\ pc' = frame.retpc
           /\ IF frame.proc = "Even"
              THEN xEven' = frame.savedXEven
              ELSE xEven' = xEven
           /\ IF frame.proc = "Odd"
              THEN xOdd' = frame.savedXOdd
              ELSE xOdd' = xOdd
           /\ UNCHANGED result

OddBody ==
    /\ pc = "OddBody"
    /\ IF xOdd = 0
       THEN
           /\ result' = FALSE
           /\ pc' = "OddReturn"
           /\ UNCHANGED <<stack, xEven, xOdd>>
       ELSE
           /\ stack' = Append(stack, [proc |-> "Odd", retpc |-> "OddReturn", savedXOdd |-> xOdd])
           /\ xEven' = xOdd - 1
           /\ pc' = "EvenBody"
           /\ UNCHANGED <<xOdd, result>>

OddReturn ==
    /\ pc = "OddReturn"
    /\ stack # <<>>
    /\ LET frame == Head(Reverse(stack))
       IN
           /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
           /\ pc' = frame.retpc
           /\ IF frame.proc = "Even"
              THEN xEven' = frame.savedXEven
              ELSE xEven' = xEven
           /\ IF frame.proc = "Odd"
              THEN xOdd' = frame.savedXOdd
              ELSE xOdd' = xOdd
           /\ UNCHANGED result

Start ==
    /\ pc = "Start"
    /\ xEven' = N
    /\ stack' = Append(stack, [proc |-> "main", retpc |-> "Done"])
    /\ pc' = "EvenBody"
    /\ UNCHANGED <<xOdd, result>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Start
    \/ EvenBody
    \/ EvenReturn
    \/ OddBody
    \/ OddReturn
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

=============================================================================