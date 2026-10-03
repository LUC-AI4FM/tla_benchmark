---------------------------- MODULE EvenOdd ----------------------------
EXTENDS Naturals, Sequences

CONSTANT N

VARIABLES pc, stack, xEven, xOdd, result

vars == <<pc, stack, xEven, xOdd, result>>

TypeOK ==
    /\ pc \in {"Init", "Even", "Odd", "Done"}
    /\ \A frame \in stack : frame = [return_pc |-> "Done"]
    /\ xEven \in Nat
    /\ xOdd \in Nat
    /\ result \in {TRUE, FALSE}

Init ==
    /\ pc = "Init"
    /\ stack = <<>>
    /\ xEven = 0
    /\ xOdd = 0
    /\ result = FALSE

\* The first step of the algorithm, calling Even(N).
Start ==
    /\ pc = "Init"
    /\ pc' = "Even"
    /\ xEven' = N
    /\ stack' = << [return_pc |-> "Done"] >>
    /\ UNCHANGED <<xOdd, result>>

\* The step corresponding to the Even procedure.
\* If xEven is 0, it's the base case: return TRUE.
\* Otherwise, it's the recursive step: call Odd(xEven - 1).
\* This is modeled as a tail call, so the stack is not modified.
Even ==
    /\ pc = "Even"
    /\ IF xEven = 0
       THEN /\ result' = TRUE
            /\ pc' = Head(stack).return_pc
            /\ stack' = Tail(stack)
            /\ UNCHANGED <<xEven, xOdd>>
       ELSE /\ pc' = "Odd"
            /\ xOdd' = xEven - 1
            /\ UNCHANGED <<stack, xEven, result>>

\* The step corresponding to the Odd procedure.
\* If xOdd is 0, it's the base case: return FALSE.
\* Otherwise, it's the recursive step: call Even(xOdd - 1).
\* This is also modeled as a tail call.
Odd ==
    /\ pc = "Odd"
    /\ IF xOdd = 0
       THEN /\ result' = FALSE
            /\ pc' = Head(stack).return_pc
            /\ stack' = Tail(stack)
            /\ UNCHANGED <<xEven, xOdd>>
       ELSE /\ pc' = "Even"
            /\ xEven' = xOdd - 1
            /\ UNCHANGED <<stack, xOdd, result>>

\* When the algorithm is done, it stutters infinitely.
Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Start
    \/ Even
    \/ Odd
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

=============================================================================