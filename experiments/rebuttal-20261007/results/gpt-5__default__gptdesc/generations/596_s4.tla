----------------------------- MODULE OneVarWF -----------------------------

EXTENDS Sequences

CONSTANTS
  CEX

VARIABLES
  x

Init ==
  x = 0

Next ==
  \/ x = 0 /\ x' \in {1, 2}
  \/ x # 0 /\ x' = 0

Spec ==
  Init /\ [][Next]_x /\ WF_x(Next)

(*
  Safety invariant: x always ranges over the intended domain.
*)
TypeInv ==
  x \in {0, 1, 2}

(*
  Liveness/temporal properties of interest:
  - Eventually stabilize away from 1 or from 2.
  - Infinitely often return to 0.
  - Negation of one of the stabilization properties.
*)
EventuallyStabilizeAwayFrom1 ==
  <>[] (x # 1)

EventuallyStabilizeAwayFrom2 ==
  <>[] (x # 2)

RepeatedReturnToZero ==
  []<> (x = 0)

NotEventuallyStabilizeAwayFrom1 ==
  ~EventuallyStabilizeAwayFrom1

(*
  Postcondition that checks a TLC-generated counterexample trace
  encoded using records, tuples, and sets.
*)
Post ==
  LET states == { [x |-> 0], [x |-> 1], [x |-> 2] }
      tau    == << [x |-> 0], [x |-> 1], [x |-> 0], [x |-> 1] >>
      pairs  == { <<[x |-> 0], [x |-> 1]>>, <<[x |-> 0], [x |-> 2]>> }
  IN /\ CEX = tau
     /\ CEX \in Seq(states)
     /\ CEX[1] = [x |-> 0]
     /\ CEX[2] \in { [x |-> 1], [x |-> 2] }
     /\ CEX[3] = [x |-> 0]
     /\ <<CEX[1], CEX[2]>> \in pairs

=============================================================================