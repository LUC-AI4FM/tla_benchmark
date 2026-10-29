------------------------------ MODULE VoucherRedeem ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    V,   \* The set of vouchers.
    H,   \* The set of voucher holders.
    C    \* The set of voucher collectors.

VARIABLES
    vState,        \* vState[v] is the state of voucher v.
    vlcState,      \* vlcState[v] is the life-cycle state of voucher v.
    hState,        \* hState[h] is the state of holder h.
    cState,        \* cState[c] is the state of collector c.
    vtpState,      \* The state of the voucher transaction provider.
    vtpTPrepared,  \* The set of Prepared messages the VTP has received.
    msgs           \* All messages ever sent. Messages are never removed.

vars == <<vState, vlcState, hState, cState, vtpState, vtpTPrepared, msgs>>

---------------------------------------------------------------------------------
\* The voucher life-cycle specification that this protocol implements.

---- MODULE VoucherLifeCycle ----
CONSTANT V
VARIABLE vState

VTypeOK == vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]

VInit == vState \in [V -> {"phantom", "valid"}]

VIssue(v)  == /\ vState[v] = "phantom"
              /\ vState' = [vState EXCEPT ![v] = "valid"]
VRedeem(v) == /\ vState[v] = "valid"
              /\ vState' = [vState EXCEPT ![v] = "redeemed"]
VCancel(v) == /\ vState[v] = "valid"
              /\ vState' = [vState EXCEPT ![v] = "cancelled"]

VNext == \E v \in V : VIssue(v) \/ VRedeem(v) \/ VCancel(v)

VSpec == VInit /\ [][VNext]_vState
====