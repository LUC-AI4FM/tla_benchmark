---------------------------- MODULE VoucherIssue ----------------------------
EXTENDS Naturals, FiniteSets

\* Embedded copy of the voucher life cycle specification, so that the
\* refinement statement below parses on its own.
---------------------------- MODULE VoucherLifeCycle ----------------------------
CONSTANT V

VARIABLES vState, vlcState

VTypeOK ==
  /\ vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"init", "working", "done"}]

VInit ==
  /\ vState = [v \in V |-> "phantom"]
  /\ vlcState = [v \in V |-> "init"]

Issue(v) ==
  /\ vState[v] = "phantom"
  /\ vlcState[v] = "init"
  /\ vState' = [vState EXCEPT ![v] = "valid"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "working"]

Transfer(v) ==
  /\ vState[v] = "valid"
  /\ UNCHANGED <<vState, vlcState>>

Redeem(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState' = [vState EXCEPT ![v] = "redeemed"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

Cancel(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState' = [vState EXCEPT ![v] = "cancelled"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VNext == \E v \in V : Issue(v) \/ Transfer(v) \/ Redeem(v) \/ Cancel(v)

VConsistent ==
  \A v \in V : vlcState[v] = "done" => vState[v] \in {"redeemed", "cancelled"}

VSpec == VInit /\ [][VNext]_<<vState, vlcState>>
=================================================================================