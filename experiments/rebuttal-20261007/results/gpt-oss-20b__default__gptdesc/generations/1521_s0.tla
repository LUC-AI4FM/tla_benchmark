MODULE CoffeeCan
EXTENDS Naturals, TLC

CONSTANTS MAX, INIT_B, INIT_W

VARIABLE s

(* Record type for the state *)
State == [B : Nat, W : Nat]

Init ==
  /\ s.B = INIT_B
  /\ s.W = INIT_W
  /\ s.B + s.W <= MAX
  /\ s.B \in Nat
  /\ s.W \in Nat
  /\ s.B <= MAX
  /\ s.W <= MAX

TwoBlack ==
  /\ s.B >= 2
  /\ s' = [s EXCEPT !.B = s.B - 1, !.W = s.W]
  /\ s'.B + s'.W < s.B + s.W

TwoWhite ==
  /\ s.W >= 2
  /\ s' = [s EXCEPT !.B = s.B + 1, !.W = s.W - 2]
  /\ s'.B + s'.W < s.B + s.W

OneEach ==
  /\ s.B >= 1
  /\ s.W >= 1
  /\ s' = [s EXCEPT !.B = s.B - 1, !.W = s.W]
  /\ s'.B + s'.W < s.B + s.W

TerminationStutter ==
  /\ s.B + s.W = 1
  /\ s' = s

NonStutter == TwoBlack \/ TwoWhite \/ OneEach

Next == NonStutter \/ TerminationStutter

TypeInv ==
  /\ s.B \in Nat
  /\ s.W \in Nat
  /\ s.B <= MAX
  /\ s.W <= MAX
  /\ s.B + s.W <= MAX

MonotonicDecrease ==
  [] (NonStutter => (s'.B + s'.W) < (s.B + s.W))

ParityInv ==
  [] ((s.W mod 2) = (INIT_W mod 2))

FinalColor ==
  [] ((s.B + s.W = 1) =>
        IF INIT_W mod 2 = 0 THEN s.B = 1 ELSE s.W = 1)

Termination ==
  []<>(s.B + s.W = 1)

Spec == Init /\ [][Next]_s /\ WF/Next

THEOREM TypeInvariantIsMaintained ==
  Spec => [] TypeInv

THEOREM MonotonicDecreaseHolds ==
  Spec => MonotonicDecrease

THEOREM ParityLoopInvariant ==
  Spec => ParityInv

THEOREM FinalColorHypothesis ==
  Spec => FinalColor

THEOREM EventualTermination ==
  Spec => Termination