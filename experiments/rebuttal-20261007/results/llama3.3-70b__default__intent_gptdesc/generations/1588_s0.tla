```
MODULE EuclideanAlgorithm
EXTENDS Integers

CONSTANTS A, N
VARIABLES x, y, initialB, halted

Init ==
  /\ initialB \in 1..N
  /\ x = A
  /\ y = initialB
  /\ halted = FALSE

Next ==
  IF halted THEN
    UNCHANGED <<x, y, initialB, halted>>
  ELSE
    IF x < y THEN
      /\ x' = y
      /\ y' = x
      /\ initialB' = initialB
      /\ halted' = halted
    ELSE
      IF y = 0 THEN
        /\ x' = x
        /\ y' = y
        /\ initialB' = initialB
        /\ halted' = TRUE
      ELSE
        /\ x' = x - y
        /\ y' = y
        /\ initialB' = initialB
        /\ halted' = halted
  END

Spec == Init /\ [][Next]_<<x, y, initialB, halted>>

Inv == 
  /\ x \in Nat
  /\ y \in Nat
  /\ initialB \in 1..N
  /\ (halted => (x = 0 \/ y = 0))
  /\ GCD(x, y) = GCD(A, initialB)

GCD(a, b) == 
  IF a = 0 THEN b
  ELSE IF b = 0 THEN a
  ELSE IF a < b THEN GCD(b, a)
  ELSE GCD(a - b, b)

THEOREM Spec => []Inv

Fairness == WF_<<x, y, initialB, halted>>(Next)

Liveness == <>[]halted

Correctness == 
  halted => (x = 0 /\ y = GCD(A, initialB)) \/ (y = 0 /\ x = GCD(A, initialB))

THEOREM Spec /\ Fairness => Liveness
THEOREM Spec => []Correctness
```