MODULE VoucherLifeCycle

CONSTANTS V

(* Possible states for vouchers and their life‑cycle machines *)
VoucherState == {"phantom", "valid", "redeemed", "cancelled"}
VLCState     == {"init", "working", "done"}

VARIABLES vState, vlcState, v2

(* Type checking predicate *)
VTypeOK ==
  /\ vState \in [V -> VoucherState]
  /\ vlcState \in [V -> VLCState]
  /\ v2 \in [V -> <<VoucherState, VLCState>>]

(* Initial condition *)
Init ==
  /\ vState = [v \in V |-> "phantom"]
  /\ vlcState = [v \in V |-> "init"]
  /\ v2 = [v \in V |-> <<"phantom", "init">>]

(* Actions *)

Issue ==
  \E v \in V :
    /\ vState[v] = "phantom"
    /\ vlcState[v] = "init"
    /\ vState' = [vState EXCEPT ![v] = "valid"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "working"]
    /\ v2' = [x \in V |-> <<vState'[x], vlcState'[x]]>

Transfer ==
  \E v \in V :
    /\ vState[v] = "valid"
    /\ vState' = vState
    /\ vlcState' = vlcState
    /\ v2' = v2

Redeem ==
  \E v \in V :
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vState' = [vState EXCEPT ![v] = "redeemed"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ v2' = [x \in V |-> <<vState'[x], vlcState'[x]]>

Cancel ==
  \E v \in V :
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vState' = [vState EXCEPT ![v] = "cancelled"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ v2' = [x \in V |-> <<vState'[x], vlcState'[x]]>

Next ==
  \/ Issue
  \/ Transfer
  \/ Redeem
  \/ Cancel

(* Stuttering action *)
Stutter ==
  /\ vState' = vState
  /\ vlcState' = vlcState
  /\ v2' = v2

VNext == Next \/ Stutter

(* Safety invariant *)
VConsistent ==
  \A