----------------------------- MODULE EuclidGCD -----------------------------

EXTENDS Naturals, Integers

CONSTANT Max
ASSUME Max = 20

VARIABLES x, y, x0, y0

vars == << x, y, x0, y0 >>

Divides(d, n) == ∃ k ∈ Nat : n = d * k

GCD(a, b) ==
  CHOOSE d ∈ 1..Max :
    /\ Divides(d, a) /\ Divides(d, b)
    /\ ∀ d2 ∈ 1..Max :
         (Divides(d2, a) /\ Divides(d2, b)) => d2 <= d

Init ==
  /\ x ∈ 1..Max
  /\ y ∈ 1..Max
  /\ x0 = x
  /\ y0 = y

Next ==
  /\ x > 0
  /\ IF x < y
        THEN /\ x' = y - x
             /\ y' = x
        ELSE /\ x' = x - y
             /\ y' = y
  /\ UNCHANGED << x0, y0 >>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Terminated == x = 0

Termination == <> Terminated

Invariant ==
  /\ x ∈ 0..Max
  /\ y ∈ 1..Max
  /\ x0 ∈ 1..Max
  /\ y0 ∈ 1..Max
  /\ (x = 0 => y = GCD(x0, y0))

=============================================================================