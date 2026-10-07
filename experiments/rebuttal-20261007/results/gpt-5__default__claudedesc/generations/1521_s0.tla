----------------------------- MODULE CoffeeCan -----------------------------

EXTENDS Naturals, Integers

CONSTANT MaxBeanCount

VARIABLE can

(*
  Helper operator: total number of beans in a can-state record.
*)
Tot(c) == c.black + c.white

(*
  Initial states: any nonnegative numbers of black and white beans whose
  total lies between 1 and MaxBeanCount (inclusive).
*)
Init ==
  can \in [black: Nat, white: Nat]
  /\ Tot(can) \in 1..MaxBeanCount

(*
  Actions corresponding to the three rules of the Coffee Can problem.
*)
BB ==
  /\ can.black >= 2
  /\ can' = [can EXCEPT !.black = @ - 1]

WW ==
  /\ can.white >= 2
  /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

BW ==
  /\ can.black >= 1
  /\ can.white >= 1
  /\ can' = [can EXCEPT !.black = @ - 1]

(*
  Termination stuttering action: when exactly one bean remains, we stutter.
*)
Termination ==
  /\ Tot(can) = 1
  /\ can' = can

(*
  Next-state relation allows any rule application or the termination stutter.
*)
Next == BB \/ WW \/ BW \/ Termination

vars == << can >>

(*
  Temporal specification: standard TLA pattern with stuttering allowed
  and weak fairness to prevent indefinite stalling while Next is enabled.
*)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Safety invariants and liveness properties to be checked                 *)
(***************************************************************************)

(*
  TypeInvariant: bean counts remain within bounds.
*)
TypeInvariant ==
  /\ can \in [black: 0..MaxBeanCount, white: 0..MaxBeanCount]
  /\ Tot(can) \in 1..MaxBeanCount

(*
  MonotonicDecrease: every non-stuttering state change strictly reduces
  the total bean count by exactly one.
*)
MonotonicDecrease ==
  [] ( (can' # can) => (Tot(can') = Tot(can) - 1) )

(*
  LoopInvariant: the parity of the white-bean count is preserved by every step.
  We define evenness arithmetically to avoid reliance on a modulo operator.
*)
IsEven(n) == \E k \in Nat: n = 2*k

LoopInvariant ==
  [] ( IsEven(can'.white) <=> IsEven(can.white) )

(*
  TerminationHypothesis: the process inevitably ends with a single bean whose
  color is determined by the initial parity of the white-bean count.
*)
OneBean     == Tot(can) = 1
FinalBlack  == OneBean /\ can.black = 1
FinalWhite  == OneBean /\ can.white = 1

TerminationHypothesis ==
  /\ ( IsEven(can.white)  => <> FinalBlack )
  /\ (~IsEven(can.white)  => <> FinalWhite )

=============================================================================