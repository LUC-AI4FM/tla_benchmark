-------------------------------- MODULE EvenOdd --------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS N

ASSUME N \in Nat

VARIABLES pc, stack, xEven, xOdd, result

vars == <<pc, stack, xEven, xOdd, result>>

Init ==
    /\ pc = "main"
    /\ stack = <<>>
    /\ xEven = 0
    /\ xOdd = 0
    /\ result = FALSE

\* Main entry point - call Even(N)
Main ==
    /\ pc = "main"
    /\ pc' = "even_start"
    /\ stack' = Append(stack, [caller |-> "done_even", localX |-> 0])
    /\ xEven' = N
    /\ UNCHANGED <<xOdd, result>>

\* Even procedure: check if xEven = 0
EvenStart ==
    /\ pc = "even_start"
    /\ IF xEven = 0
       THEN /\ result' = TRUE
            /\ pc' = "even_return"
            /\ UNCHANGED <<stack, xEven, xOdd>>
       ELSE /\ pc' = "even_call_odd"
            /\ UNCHANGED <<stack, xEven, xOdd, result>>

\* Even procedure: call Odd(xEven - 1)
EvenCallOdd ==
    /\ pc = "even_call_odd"
    /\ pc' = "odd_start"
    /\ stack' = Append(stack, [caller |-> "even_return", localX |-> xEven])
    /\ xOdd' = xEven - 1
    /\ UNCHANGED <<xEven, result>>

\* Even procedure: return
EvenReturn ==
    /\ pc = "even_return"
    /\ Len(stack) > 0
    /\ LET frame == Head(stack)
       IN /\ pc' = frame.caller
          /\ stack' = Tail(stack)
          /\ UNCHANGED <<xEven, xOdd, result>>

\* Odd procedure: check if xOdd = 0
OddStart ==
    /\ pc = "odd_start"
    /\ IF xOdd = 0
       THEN /\ result' = FALSE
            /\ pc' = "odd_return"
            /\ UNCHANGED <<stack, xEven, xOdd>>
       ELSE /\ pc' = "odd_call_even"
            /\ UNCHANGED <<stack, xEven, xOdd, result>>

\* Odd procedure: call Even(xOdd - 1)
OddCallEven ==
    /\ pc = "odd_call_even"
    /\ pc' = "even_start"
    /\ stack' = Append(stack, [caller |-> "odd_return", localX |-> xOdd])
    /\ xEven' = xOdd - 1
    /\ UNCHANGED <<xOdd, result>>

\* Odd procedure: return
OddReturn ==
    /\ pc = "odd_return"
    /\ Len(stack) > 0
    /\ LET frame == Head(stack)
       IN /\ pc' = frame.caller
          /\ stack' = Tail(stack)
          /\ UNCHANGED <<xEven, xOdd, result>>

\* Final return from Even back to main
DoneEven ==
    /\ pc = "done_even"
    /\ pc' = "Done"
    /\ UNCHANGED <<stack, xEven, xOdd, result>>

\* Allow stuttering after termination to avoid deadlock
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Main
    \/ EvenStart
    \/ EvenCallOdd
    \/ EvenReturn
    \/ OddStart
    \/ OddCallEven
    \/ OddReturn
    \/ DoneEven
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety invariant: result correctly indicates whether N is even
ResultCorrect ==
    pc = "Done" => (result = (N % 2 = 0))

\* Safety invariant: pc is always a valid control location
TypeInvariant ==
    /\ pc \in {"main", "even_start", "even_call_odd", "even_return",
               "odd_start", "odd_call_even", "odd_return", "done_even", "Done"}
    /\ xEven \in Nat
    /\ xOdd \in Nat
    /\ result \in BOOLEAN

\* Liveness property: execution eventually reaches termination
EventualTermination == <>(pc = "Done")

================================================================================