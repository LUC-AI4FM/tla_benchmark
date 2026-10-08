------------------------------- MODULE EvenOdd -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES pc, stack, xEven, xOdd, result

Init == 
  /\ pc = "Start"
  /\ stack = << >>
  /\ xEven = 0
  /\ xOdd = 0
  /\ result = FALSE

Even ==
  CASE pc = "Even" ->
    IF xEven = N THEN
      /\ result' = (N % 2 = 0)
      /\ pc' = "Done"
    ELSE
      /\ stack' = Append(stack, <<pc, xEven, xOdd>>)
      /\ pc' = "Odd"
      /\ xEven' = xEven + 1
      /\ UNCHANGED <<xOdd, result>>
    ENDIF

Odd ==
  CASE pc = "Odd" ->
    IF xOdd = N THEN
      /\ result' = (N % 2 <> 0)
      /\ pc' = "Done"
    ELSE
      /\ stack' = Append(stack, <<pc, xEven, xOdd>>)
      /\ pc' = "Even"
      /\ xOdd' = xOdd + 1
      /\ UNCHANGED <<xEven, result>>
    ENDIF

Next == 
  \/ EVEN
  \/ ODD
  \/ \E s \in stack : 
       LET topPc = Fst(s)
           topXEven = Snd(s)
           topXOdd = Tl(Tl(s))[1] 
       IN /\ pc' = topPc
          /\ IF topPc = "Even" THEN xEven' = topXEven ELSE xOdd' = topXOdd
          /\ stack' = Head(stack)
          /\ UNCHANGED <<result>>

Spec == 
  /\ Init
  /\ [][Next]_<<pc, stack, xEven, xOdd, result>>
  /\ WF_[Next]_<<pc, stack, xEven, xOdd, result>>
  /\ <><pc = "Done">>_<<pc, stack, xEven, xOdd, result>>

=============================================================================