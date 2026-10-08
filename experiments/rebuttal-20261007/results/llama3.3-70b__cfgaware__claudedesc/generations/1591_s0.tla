---------------------------- MODULE EvenOdd ----------------------------
EXTENDS Integers, Sequences

CONSTANT N

VARIABLE pc, result, stack, xEven, xOdd

Init == 
  (pc = "Start") /\ 
  (result = FALSE) /\ 
  (stack = <<>> ) /\ 
  (xEven = 0) /\ 
  (xOdd = 0)

CallEven(n) == 
  (* Precondition: n > 0 *)
  (pc' = "Even") /\ 
  (stack' = Append(stack, n)) /\ 
  (xEven' = n) /\ 
  UNCHANGED <<result, xOdd, pc>>

EvenBody == 
  IF xEven = 0 THEN
    (* Base case: set result to TRUE *)
    (pc' = "Done") /\ 
    (result' = TRUE) /\ 
    UNCHANGED <<stack, xEven, xOdd>>
  ELSE 
    (* Recursive call to Odd *)
    CallOdd(xEven - 1)

CallOdd(n) == 
  (* Precondition: n > 0 *)
  (pc' = "Odd") /\ 
  (stack' = Append(stack, n)) /\ 
  (xOdd' = n) /\ 
  UNCHANGED <<result, xEven, pc>>

OddBody == 
  IF xOdd = 0 THEN
    (* Base case: set result to FALSE *)
    (pc' = "Done") /\ 
    (result' = FALSE) /\ 
    UNCHANGED <<stack, xEven, xOdd>>
  ELSE 
    (* Recursive call to Even *)
    CallEven(xOdd - 1)

Next == 
  IF pc = "Start" THEN 
    CallEven(N)
  ELSE IF pc = "Even" THEN 
    EvenBody
  ELSE IF pc = "Odd" THEN 
    OddBody
  ELSE 
    UNCHANGED <<pc, result, stack, xEven, xOdd>>

Spec == Init /\ [][Next]_<<pc, result, stack, xEven, xOdd>>
                   /\ WF_<<pc, result, stack, xEven, xOdd>>(Next)

Termination == <> (pc = "Done")

THEOREM Spec => Termination
=============================================================================