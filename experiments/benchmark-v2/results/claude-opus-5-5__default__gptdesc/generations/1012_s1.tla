------------------------------ MODULE VoucherCancel ------------------------------
EXTENDS Naturals, FiniteSets

-----------------------------------------------------------------------------
\* Imported voucher life cycle specification (defined as a nested module so
\* that the specification is self-contained).
-----------------------------------------------------------------------------
---------------------------- MODULE VoucherLifeCycle ------------------------
CONSTANT V          \* The set of vouchers
VARIABLES vState,   \* vState[v] is the state of voucher v
          vlcState  \* vlcState[v] is the state of the life cycle of voucher v

VTypeOK ==
  /\ vState   \in [V -> {"valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"working", "done"}]

VInit ==
  /\ vState   = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]

Transfer(v) ==
  /\ vState[v] = "valid"
  /\ UNCHANGED <<vState, vlcState>>

Redeem(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState'   = [vState EXCEPT ![v] = "redeemed"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

Cancel(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState'   = [vState EXCEPT ![v] = "cancelled"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VNext == \E v \in V : Transfer(v) \/ Redeem(v) \/ Cancel(v)

VSpec == VInit /\ [][VNext]_<<vState, vlcState>>
=============================================================================