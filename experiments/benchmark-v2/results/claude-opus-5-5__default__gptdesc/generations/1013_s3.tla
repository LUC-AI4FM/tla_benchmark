------------------------------ MODULE VoucherIssue ------------------------------
EXTENDS Integers

-------------------------- MODULE VoucherLifeCycle ----------------------------
CONSTANT V

VARIABLES vState, vlcState

VLCTypeOK ==
  /\ vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"init", "working", "done"}]

VLCInit ==
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

VLCNext ==
  \E v \in V : Issue(v) \/ Transfer(v) \/ Redeem(v) \/ Cancel(v)

VLCSpec == VLCInit /\ [][VLCNext]_<<vState, vlcState>>

VLCConsistent ==
  \A v \in V : \/ /\ vState[v] = "phantom"
                  /\ vlcState[v] = "init"
               \/ /\ vState[v] = "valid"
                  /\ vlcState[v] = "working"
               \/ /\ vState[v] \in {"redeemed", "cancelled"}
                  /\ vlcState[v] = "done"
===============================================================================