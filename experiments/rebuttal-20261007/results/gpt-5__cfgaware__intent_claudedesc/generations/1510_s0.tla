---------------------------- MODULE CaseUpdateDemo ----------------------------

EXTENDS Naturals

VARIABLES x, f

Dom == {0, 1, 2}
SpecialVal == 1
DesignatedKey == 2
DesignatedConst == 42

Init ==
  /\ x \in Dom
  /\ x = 0
  /\ f = [i \in Dom |-> 0]

Next ==
  /\ x' = x
  /\ f' = [ f EXCEPT
              ![DesignatedKey] = CASE x = SpecialVal -> DesignatedConst [] OTHER -> @
          ]

Spec == Init /\ [][Next]_<<x, f>>

=============================================================================