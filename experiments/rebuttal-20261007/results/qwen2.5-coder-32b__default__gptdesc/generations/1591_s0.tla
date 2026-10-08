------------------------------- MODULE EvenOdd -------------------------------

EXTENDS Integers, Sequences, TLC

CONSTANTS N

VARIABLES pc, stack, xEven, xOdd, result

Init == 
  /\ pc = "Start"
  /\ stack = << >>
  /\ xEven = 0
  /\ xOdd = 0
  /\ result = FALSE

Next ==
  \/ /\ pc = "Start"
     /\ (N % 2 = 0) -> pc' = "Even" 
        /\ stack' = Append(stack, "Start")
        /\ xEven' = N
        /\ UNCHANGED <<xOdd, result>>
     /\ (N % 2 # 0) -> pc' = "Odd"
        /\ stack' = Append(stack, "Start")
        /\ xOdd' = N
        /\ UNCHANGED <<xEven, result>>
  \/ /\ pc = "Even"
     /\ xEven > 0
     /\ pc' = "EvenRec"
        /\ stack' = Append(stack, "Even")
        /\ xEven' = xEven - 2
        /\ UNCHANGED <<xOdd, result>>
  \/ /\ pc = "Even"
     /\ xEven = 0
     /\ pc' = "Done"
        /\ result' = TRUE
        /\ UNCHANGED <<stack, xEven, xOdd>>
  \/ /\ pc = "EvenRec"
     /\ xEven > 0
     /\ pc' = "EvenRec"
        /\ stack' = Append(stack, "EvenRec")
        /\ xEven' = xEven - 2
        /\ UNCHANGED <<xOdd, result>>
  \/ /\ pc = "EvenRec"
     /\ xEven = 0
     /\ LET returnPc == Head(Rev(stack)) IN
        /\ pc' = returnPc
        /\ stack' = Tail(stack)
        /\ result' = TRUE
        /\ UNCHANGED <<xEven, xOdd>>
  \/ /\ pc = "Odd"
     /\ xOdd > 0
     /\ pc' = "OddRec"
        /\ stack' = Append(stack, "Odd")
        /\ xOdd' = xOdd - 2
        /\ UNCHANGED <<xEven, result>>
  \/ /\ pc = "Odd"
     /\ xOdd = 1
     /\ pc' = "Done"
        /\ result' = FALSE
        /\ UNCHANGED <<stack, xEven, xOdd>>
  \/ /\ pc = "OddRec"
     /\ xOdd > 0
     /\ pc' = "OddRec"
        /\ stack' = Append(stack, "OddRec")
        /\ xOdd' = xOdd - 2
        /\ UNCHANGED <<xEven, result>>
  \/ /\ pc = "OddRec"
     /\ xOdd = 1
     /\ LET returnPc == Head(Rev(stack)) IN
        /\ pc' = returnPc
        /\ stack' = Tail(stack)
        /\ result' = FALSE
        /\ UNCHANGED <<xEven, xOdd>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<pc', stack', xEven', xOdd', result'>>

Spec ==
  /\ Init
  /\ [][Next]_<<pc, stack, xEven, xOdd, result>>
  /\ WF_[Next]_<<pc, stack, xEven, xOdd, result>>

=============================================================================