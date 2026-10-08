---- MODULE CoffeeCan ----
CONSTANT MaxBeanCount

VARIABLE can

(* Record representing the coffee can: [black : Nat, white : Nat] *)

Initial ==
  /\ 1 <= can.black + can.white
  /\ can.black + can.white <= MaxBeanCount
  /\ can.black >= 0
  /\ can.white >= 0

PickTwoBlack ==
  /\ can.black >= 2
  /\ can' = [can EXCEPT !.black = @ - 1]

PickTwoWhite ==
  /\ can.white >= 2
  /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

PickOneEach ==
  /\ can.black >= 1
  /\ can.white >= 1
  /\ can' = [can EXCEPT !.black = @ - 1]

Termination ==
  /\ (can.black + can.white) = 1
  /\ can' = can

Stutter ==
  /\ can' = can

Next == PickTwoBlack \/ PickTwoWhite \/ PickOneEach \/ Termination \/ Stutter

Spec == Initial /\ [][Next]_can /\ WF_vars(Next)

TypeInvariant ==
  /\ 0 <= can.black
  /\ 0 <= can.white
  /\ can.black + can.white <= MaxBeanCount

MonotonicDecrease ==
  [] ((can' = can) \/ (can.black + can.white > can'.black + can'.white))

LoopInvariant ==
  [] ((can.white \bmod 2) = (can'.white \bmod 2))

TerminationHypothesis ==
  [] ((can.white \bmod 2 = 0) => <> (can.black = 1 /\ can.white = 0))
  /\ [] ((can.white \bmod 2 = 1) => <> (can.black = 0 /\ can.white = 1))

====