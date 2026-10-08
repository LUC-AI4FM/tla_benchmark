----------------------------- MODULE CaseOtherUpdate -----------------------------

EXTENDS Integers

CONSTANTS S, UpdateIndex, TriggerValue, K

ASSUME S \subseteq Int /\ S /= {} /\ UpdateIndex \in S /\ TriggerValue \in S /\ K \in Int

VARIABLES x, f

Init ==
  /\ x \in S
  /\ f = [s \in S |-> 0]

Next ==
  /\ UNCHANGED x
  /\ f' = [f EXCEPT
             ![UpdateIndex] =
               CASE x = TriggerValue -> K
                    [] OTHER -> @]

Spec == Init /\ [][Next]_<<x, f>>

=============================================================================