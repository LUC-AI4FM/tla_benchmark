---------------------------- MODULE EvenOdd ----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N

VARIABLES pc, stack, xEven, xOdd, result

vars == <<pc, stack, xEven, xOdd, result>>

Init ==
    /\ pc = "MainCall"
    /\ stack = <<>>
    /\ xEven = 0
    /\ xOdd = 0
    /\ result = FALSE

\* Main entry point: call Even(N)
MainCall ==
    /\ pc = "MainCall"
    /\ pc' = "EvenStart"
    /\ xEven' = N
    /\ stack' = Append(stack, [proc |-> "Main", x |-> 0])
    /\ UNCHANGED <<xOdd, result>>

\* Even procedure: if xEven = 0 then return TRUE, else call Odd(xEven - 1)
EvenStart ==
    /\ pc = "EvenStart"
    /\ IF xEven = 0
       THEN
           /\ result' = TRUE
           /\ pc' = "EvenReturn"
           /\ UNCHANGED <<stack, xEven, xOdd>>
       ELSE
           /\ xOdd' = xEven - 1
           /\ stack' = Append(stack, [proc |-> "Even", x |-> xEven])
           /\ pc' = "OddStart"
           /\ UNCHANGED <<xEven, result>>

\* Return from Even procedure
EvenReturn ==
    /\ pc = "EvenReturn"
    /\ Len(stack) > 0
    /\ LET frame == stack[Len(stack)]
       IN IF frame.proc = "Main"
          THEN
              /\ pc' = "Done"
              /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
              /\ UNCHANGED <<xEven, xOdd, result>>
          ELSE IF frame.proc = "Odd"
          THEN
              /\ pc' = "OddReturn"
              /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
              /\ xOdd' = frame.x
              /\ UNCHANGED <<xEven, result>>
          ELSE
              /\ pc' = "EvenReturn"
              /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
              /\ xEven' = frame.x
              /\ UNCHANGED <<xOdd, result>>

\* Odd procedure: if xOdd = 0 then return FALSE, else call Even(xOdd - 1)
OddStart ==
    /\ pc = "OddStart"
    /\ IF xOdd = 0
       THEN
           /\ result' = FALSE
           /\ pc' = "OddReturn"
           /\ UNCHANGED <<stack, xEven, xOdd>>
       ELSE
           /\ xEven' = xOdd - 1
           /\ stack' = Append(stack, [proc |-> "Odd", x |-> xOdd])
           /\ pc' = "EvenStart"
           /\ UNCHANGED <<xOdd, result>>

\* Return from Odd procedure
OddReturn ==
    /\ pc = "OddReturn"
    /\ Len(stack) > 0
    /\ LET frame == stack[Len(stack)]
       IN IF frame.proc = "Main"
          THEN
              /\ pc' = "Done"
              /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
              /\ UNCHANGED <<xEven, xOdd, result>>
          ELSE IF frame.proc = "Even"
          THEN
              /\ pc' = "EvenReturn"
              /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
              /\ xEven' = frame.x
              /\ UNCHANGED <<xOdd, result>>
          ELSE
              /\ pc' = "OddReturn"
              /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
              /\ xOdd' = frame.x
              /\ UNCHANGED <<xEven, result>>

\* Allow infinite stuttering after termination
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ MainCall
    \/ EvenStart
    \/ EvenReturn
    \/ OddStart
    \/ OddReturn
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety invariant: result correctly indicates whether N is even
TypeInvariant ==
    /\ pc \in {"MainCall", "EvenStart", "EvenReturn", "OddStart", "OddReturn", "Done"}
    /\ xEven \in Nat
    /\ xOdd \in Nat
    /\ result \in BOOLEAN

\* The result is correct when we reach Done
CorrectResult ==
    pc = "Done" => (result = ((N % 2) = 0))

\* Liveness property: eventual termination
Termination == <>(pc = "Done")

==========================================================================