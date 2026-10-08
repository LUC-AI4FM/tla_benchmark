---------------------------- MODULE EuclideanGCD ----------------------------
EXTENDS Integers

CONSTANT MaxValue
VARIABLES x, y

Spec == 
  /\ x \in 1..MaxValue
  /\ y \in 1..MaxValue
  /\ [][
      /\ (x = 0) => y = GCD(<<x_0, y_0>>)
      /\ (y = 0) => x = GCD(<<x_0, y_0>>)
      /\ IF x > y THEN 
          IF x = y + 1 THEN 
            y' = y /\ x' = 0
          ELSE 
            x' = x - y /\ y' = y
        ELSE 
          IF y = x + 1 THEN 
            x' = x /\ y' = 0
          ELSE 
            x' = x /\ y' = y - x
  ]

Termination == <>(x = 0) \/ <>(y = 0)

Invariant == 
  /\ x \in Nat
  /\ y \in Nat
  /\ GCD(<<x, y>>) = GCD(<<x_0, y_0>>)
  
GCD(p) == IF p[1] = 0 THEN p[2] ELSE GCD(<<p[2], p[1] % p[2]>>)

THEOREM Spec => []Invariant
THEOREM Spec => Termination
=============================================================================