------------------------------ MODULE CoffeeCan ------------------------------

EXTENDS Naturals, Integers

CONSTANT MaxN

VARIABLES b, w, w0

vars == << b, w, w0 >>

Total == b + w

IsEven(n) == n % 2 = 0

Init ==
  /\ b \in 0..MaxN
  /\ w \in 0..MaxN
  /\ Total \in 1..MaxN
  /\ w0 = w

TwoBlack ==
  /\ b >= 2
  /\ b' = b - 1
  /\ w' = w

TwoWhite ==
  /\ w >= 2
  /\ b' = b + 1
  /\ w' = w - 2

Mixed ==
  /\ b >= 1 /\ w >= 1
  /\ b' = b - 1
  /\ w' = w

Step == TwoBlack \/ TwoWhite \/ Mixed

Next ==
  /\ Step
  /\ w0' = w0

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Term == (Total = 1)

(*
 Safety and liveness properties to be checked with TLC
*)

TypeOK ==
  /\ b \in 0..MaxN
  /\ w \in 0..MaxN
  /\ w0 \in 0..MaxN
  /\ Total \in 0..MaxN

StepDecreases ==
  [] (Next => (Total' = Total - 1))

WhiteParityStep ==
  [] (Next => (w' % 2 = w % 2))

WhiteParityState ==
  [] (w % 2 = w0 % 2)

Terminates ==
  <> Term

TerminalColor ==
  [] (Term =>
        IF IsEven(w0)
          THEN /\ b = 1 /\ w = 0
          ELSE /\ b = 0 /\ w = 1)

=============================================================================