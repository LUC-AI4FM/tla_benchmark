---- MODULE CoffeeCan ----
EXTENDS Naturals, Integers

CONSTANTS Max, InitBlack, InitWhite

VARIABLES can

Total(c) == c.black + c.white
Parity(n) == n % 2

TypeInv ==
  /\ can \in [black: 0..Max, white: 0..Max]
  /\ Total(can) \in 1..Max

Init ==
  /\ can = [black |-> InitBlack, white |-> InitWhite]
  /\ InitBlack \in 0..Max
  /\ InitWhite \in 0..Max
  /\ Total(can) \in 1..Max

TakeWW ==
  /\ can.white >= 2
  /\ can' = [can EXCEPT !.white = @ - 2, !.black = @ + 1]

TakeBB ==
  /\ can.black >= 2
  /\ can' = [can EXCEPT !.black = @ - 1]

TakeWB ==
  /\ can.white >= 1
  /\ can.black >= 1
  /\ can' = [can EXCEPT !.black = @ - 1]

Remove == TakeWW \/ TakeBB \/ TakeWB

Terminate ==
  /\ Total(can) = 1
  /\ can' = can

Next == Remove \/ Terminate

Spec == Init /\ [][Next]_can /\ WF_can(Remove)

Monotonic ==
  [] (Total(can') = Total(can) \/ Total(can') = Total(can) - 1)

StrictDecreaseWhenNotTerminal ==
  [] ( (Total(can) > 1) => (Total(can') = Total(can) - 1) )

ParityInv ==
  [] (Parity(can.white) = Parity(InitWhite))

Termination ==
  <> (Total(can) = 1)

FinalWhiteIffOddInit ==
  [] ( (Total(can) = 1) => ((can.white = 1) <=> (Parity(InitWhite) = 1)) )

====