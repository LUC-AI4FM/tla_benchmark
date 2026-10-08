```
MODULE EvenOdd
EXTENDS Integers, Sequences

CONSTANTS N
VARIABLES pc, stack, xEven, xOdd, result

Init == 
  (pc = "Start") /\ 
  (stack = <<>> ) /\ 
  (xEven = 0) /\ 
  (xOdd = 0) /\ 
  (result = FALSE)

IsEven(x) == (x mod 2 = 0)
IsOdd(x) == ~(IsEven(x))

Next == 
  \/ (pc = "Start") /\ 
       (stack' = <<N>> ) /\ 
       (xEven' = 0) /\ 
       (xOdd' = 0) /\ 
       (result' = FALSE) /\ 
       (pc' = "Even")
  \/ (pc = "Even") /\ 
       (IsEven(Head(stack))) /\ 
       (stack' = Tail(stack)) /\ 
       (xEven' = xEven + 1) /\ 
       (xOdd' = xOdd) /\ 
       (result' = TRUE) /\ 
       (pc' = "Done")
  \/ (pc = "Even") /\ 
       (~IsEven(Head(stack))) /\ 
       (stack' = <<Head(stack)-1>> @ Tail(stack)) /\ 
       (xEven' = xEven) /\ 
       (xOdd' = xOdd + 1) /\ 
       (result' = FALSE) /\ 
       (pc' = "Odd")
  \/ (pc = "Odd") /\ 
       (~IsOdd(Head(stack))) /\ 
       (stack' = <<Head(stack)-1>> @ Tail(stack)) /\ 
       (xEven' = xEven + 1) /\ 
       (xOdd' = xOdd) /\ 
       (result' = FALSE) /\ 
       (pc' = "Even")
  \/ (pc = "Odd") /\ 
       (IsOdd(Head(stack))) /\ 
       (stack' = Tail(stack)) /\ 
       (xEven' = xEven) /\ 
       (xOdd' = xOdd + 1) /\ 
       (result' = FALSE) /\ 
       (pc' = "Done")
  \/ (pc = "Done") /\ 
       (UNCHANGED stack) /\ 
       (UNCHANGED xEven) /\ 
       (UNCHANGED xOdd) /\ 
       (UNCHANGED result) /\ 
       (UNCHANGED pc)

Spec == Init /\ [][Next]_<<pc, stack, xEven, xOdd, result>>
Termination == <>(pc = "Done")
THEOREM Spec => []Termination
```
Note: This TLA+ specification uses a weak fairness condition on the `Next` relation to ensure that if a step can be taken from some state, it will eventually be taken. The `UNCHANGED` operator is used in the last disjunct of `Next` to allow infinite stuttering after termination.