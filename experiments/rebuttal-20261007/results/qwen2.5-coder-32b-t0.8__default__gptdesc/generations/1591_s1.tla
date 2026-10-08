------------------------------- MODULE EvenOdd -------------------------------

EXTENDS Integers, Sequences

CONSTANTS N

VARIABLES pc, stack, xEven, xOdd, result

Init == 
  /\ pc = "Start"
  /\ stack = << >> 
  /\ xEven = FALSE 
  /\ xOdd = FALSE
  /\ result = FALSE

Next ==
  \/ \* Even procedure
     (pc = "Start" /\ N >= 0 /\ 
      \/ /\ N = 0 
         /\ pc' = "Done"
         /\ result' = TRUE
         /\ UNCHANGED <<stack, xEven, xOdd>>
       \/ /\ N > 0
          /\ pc' = "CallOdd"
          /\ stack' = Append(stack, <<"Even", N>>)
          /\ UNCHANGED <<xEven, xOdd, result>>)
  \/ \* Call to Odd from Even
     (pc = "CallOdd" /\ 
      /\ LET top == Head(stack) IN
         /\ pc' = "Odd"
         /\ stack' = Tail(stack)
         /\ xOdd' = TRUE
         /\ xEven' = FALSE
         /\ UNCHANGED <<result>>)
  \/ \* Odd procedure
     (pc = "Odd" /\ 
      /\ LET top == Head(stack) IN
         /\ CASE top[2] = 1 ->
              pc' = "Done"
              /\ result' = FALSE
              /\ stack' = Tail(Tail(stack))
              /\ UNCHANGED <<xEven, xOdd>>
            [] top[2] > 1 ->
              pc' = "CallEven"
              /\ stack' = Append(Append(stack, <<"Odd", top[2] - 1>>), <<top[0], top[1]>>)
              /\ UNCHANGED <<xEven, xOdd, result>>)
  \/ \* Call to Even from Odd
     (pc = "CallEven" /\ 
      /\ LET top == Head(stack) IN
         /\ pc' = "Even"
         /\ stack' = Tail(stack)
         /\ xEven' = TRUE
         /\ xOdd' = FALSE
         /\ UNCHANGED <<result>>)

Spec ==
  /\ Init
  /\ [][Next]_<<pc, stack, xEven, xOdd, result>>
  /\ WF_[Next]_<<pc, stack, xEven, xOdd, result>>
  /\ <>(pc = "Done")

=============================================================================