------------------------------ MODULE VoucherLifecycle ------------------------------

EXTENDS TLC

CONSTANTS

VARIABLES V, v2

Ids == {0, 1}
Owners == {"Alice", "Bob"}
NoneOwner == "None"

VoucherStates == {"PHANTOM", "VALID", "REDEEMED", "CANCELLED"}

VoucherType == [id: Ids, owner: Owners \cup {NoneOwner}]

VTypeOK ==
  /\ V \in VoucherType
  /\ v2 \in VoucherStates

VConsistent ==
  /\ (v2 = "PHANTOM") <=> (V.owner = NoneOwner)

Init ==
  /\ v2 = "PHANTOM"
  /\ V \in VoucherType
  /\ V.owner = NoneOwner

Issue ==
  /\ v2 = "PHANTOM"
  /\ v2' = "VALID"
  /\ \E o \in Owners:
       V' = [V EXCEPT !.owner = o]

Redeem ==
  /\ v2 = "VALID"
  /\ v2' = "REDEEMED"
  /\ V' = V

Cancel ==
  /\ v2 = "VALID"
  /\ v2' = "CANCELLED"
  /\ V' = V

Transfer ==
  /\ v2 = "VALID"
  /\ UNCHANGED <<V, v2>>

Next ==
  Issue \/ Redeem \/ Cancel \/ Transfer

VSpec ==
  /\ VTypeOK
  /\ VConsistent
  /\ Init
  /\ [][Next]_<<V, v2>>

THEOREM TypeAndConsistencyAlwaysPreserved ==
  VSpec => [](VTypeOK /\ VConsistent)
PROOF OBVIOUS

=============================================================================