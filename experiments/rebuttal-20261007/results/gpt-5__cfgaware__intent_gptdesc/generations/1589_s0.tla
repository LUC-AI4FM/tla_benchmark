---- MODULE Euclid ----
EXTENDS Naturals

CONSTANT Max \* finite upper bound for model checking

VARIABLES x, y, a0, b0, pc

Running == pc = "Run"
Halted  == pc = "Done"

Divides(d, n) == \E k \in Nat : n = d * k
Divs(n) == { d \in 1..Max : Divides(d, n) }
GCD(m, n) ==
  CHOOSE g \in (Divs(m) \cap Divs(n)) :
    \A d \in (Divs(m) \cap Divs(n)) : d <= g

Init ==
  /\ a0 \in 1..Max
  /\ b0 \in 1..Max
  /\ x = a0
  /\ y = b0
  /\ pc = "Run"

Swap ==
  /\ pc = "Run"
  /\ x < y
  /\ x' = y
  /\ y' = x
  /\ UNCHANGED << a0, b0, pc >>

Sub ==
  /\ pc = "Run"
  /\ x > y
  /\ y > 0
  /\ x' = x - y
  /\ UNCHANGED << y, a0, b0, pc >>

EqualToHalt ==
  /\ pc = "Run"
  /\ x = y
  /\ x > 0
  /\ x' = x
  /\ y' = 0
  /\ pc' = "Done"
  /\ UNCHANGED << a0, b0 >>

HaltZero ==
  /\ pc = "Run"
  /\ (x = 0 \/ y = 0)
  /\ pc' = "Done"
  /\ UNCHANGED << x, y, a0, b0 >>

DoneStutter ==
  /\ pc = "Done"
  /\ UNCHANGED << x, y, a0, b0, pc >>

Next == Swap \/ Sub \/ EqualToHalt \/ HaltZero \/ DoneStutter

vars == << x, y, a0, b0, pc >>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
  /\ x \in 0..Max
  /\ y \in 0..Max
  /\ a0 \in 1..Max
  /\ b0 \in 1..Max
  /\ pc \in {"Run", "Done"}

RunningPositive ==
  Running => /\ x \in 1..Max /\ y \in 1..Max

GCDInv == GCD(x, y) = GCD(a0, b0)

SwapOK == (x < y) => GCD(y, x) = GCD(x, y)

HaltCorrect ==
  Halted =>
    \/ /\ x = 0 /\ y = GCD(a0, b0)
       /\ y \in 1..Max
    \/ /\ y = 0 /\ x = GCD(a0, b0)
       /\ x \in 1..Max

Invariant == TypeOK /\ RunningPositive /\ GCDInv /\ SwapOK /\ HaltCorrect

Termination == <>Halted
====