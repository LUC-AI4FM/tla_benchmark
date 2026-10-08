---- MODULE CoffeeCan ----
EXTENDS Naturals

CONSTANT MaxBeanCount

VARIABLE can

(*
  can is a record with fields:
    - black: Nat
    - white: Nat
*)

Total(c) == c.black + c.white

TypeOK(c) ==
  /\ c \in [black: Nat, white: Nat]
  /\ Total(c) \in 0..MaxBeanCount

Init ==
  /\ can \in [black: Nat, white: Nat]
  /\ Total(can) \in 1..MaxBeanCount

BB ==
  /\ can.black >= 2
  /\ can' = [can EXCEPT !.black = @ - 1, !.white = @]

WW ==
  /\ can.white >= 2
  /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

BW ==
  /\ can.black >= 1
  /\ can.white >= 1
  /\ can' = [can EXCEPT !.black = @ - 1, !.white = @]

Next == BB \/ WW \/ BW

Termination ==
  /\ Total(can) = 1
  /\ UNCHANGED can

Act == Next \/ Termination

Spec ==
  /\ Init
  /\ [][Act]_can
  /\ WF_can(Next)

TypeInvariant == TypeOK(can)

MonotonicDecrease ==
  [](Next => Total(can') = Total(can) - 1)

LoopInvariant ==
  []((can'.white % 2) = (can.white % 2))

OneBlack == /\ can.black = 1 /\ can.white = 0
OneWhite == /\ can.black = 0 /\ can.white = 1

TerminationHypothesis ==
  /\ ((can.white % 2) = 0) ~> OneBlack
  /\ ((can.white % 2) = 1) ~> OneWhite

====