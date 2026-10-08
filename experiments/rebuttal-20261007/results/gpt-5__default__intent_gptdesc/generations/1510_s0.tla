----------------------------- MODULE SimpleTransformer -----------------------------

EXTENDS Integers

CONSTANTS
  Dist, \* Distinguished index
  K     \* Fixed constant to write

Index == 0..4

ASSUME Dist \in Index
ASSUME K \in Int

VARIABLES c, v

Vars == << c, v >>

Init ==
  /\ c \in Index
  /\ v = [ i \in Index |-> 0 ]

Next ==
  /\ c' = c
  /\ v' = IF c = Dist
          THEN [v EXCEPT ![Dist] = K]
          ELSE v

Spec == Init /\ [][Next]_Vars

(*
  Safety invariants and temporal properties:
  1) The control value never changes.
  2) The vector entries are always integers.
  3) If the control equals the distinguished value, then in the next state
     the corresponding vector entry equals the fixed constant.
  4) If the control does not equal the distinguished value, then all vector entries
     remain equal to their previous values.
  No additional fairness is asserted.
*)

TypeInv ==
  [] (c \in Index /\ v \in [Index -> Int])

ControlConstant ==
  [] UNCHANGED c

UpdateWhenEqual ==
  [] (c = Dist => v' = [v EXCEPT ![Dist] = K])

NoChangeWhenNotEqual ==
  [] (c # Dist => v' = v)

SafetyProps ==
  TypeInv /\ ControlConstant /\ UpdateWhenEqual /\ NoChangeWhenNotEqual

THEOREM Spec => SafetyProps

=============================================================================