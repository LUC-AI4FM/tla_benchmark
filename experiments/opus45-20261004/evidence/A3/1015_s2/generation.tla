---------------------------- MODULE VoucherLifeCycle ----------------------------
(***************************************************************************)
(* This specification models the life cycle of vouchers, based on RFC 3506 *)
(* with the tuple component decoupled. Each voucher begins in a "phantom"  *)
(* state before issuance, may become "valid", and can then either be       *)
(* redeemed or cancelled. Transfer is allowed as a stuttering action while *)
(* the voucher remains valid.                                              *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS Vouchers, Holders

VARIABLES 
    voucherState,    \* Function from Vouchers to their lifecycle state
    voucherHolder,   \* Function from Vouchers to their current holder (or "none")
    machineState     \* Function from Vouchers to the lifecycle machine state

(***************************************************************************)
(* Lifecycle states for vouchers                                           *)
(***************************************************************************)
VoucherStates == {"phantom", "valid", "redeemed", "cancelled"}

(***************************************************************************)
(* Machine states corresponding to lifecycle phases                        *)
(***************************************************************************)
MachineStates == {"unissued", "active", "terminal"}

(***************************************************************************)
(* Type correctness invariant                                              *)
(***************************************************************************)
TypeOK ==
    /\ voucherState \in [Vouchers -> VoucherStates]
    /\ voucherHolder \in [Vouchers -> Holders \cup {"none"}]
    /\ machineState \in [Vouchers -> MachineStates]

(***************************************************************************)
(* Consistency invariant relating voucher state to machine state           *)
(***************************************************************************)
Consistency ==
    \A v \in Vouchers:
        /\ (voucherState[v] = "phantom") => (machineState[v] = "unissued")
        /\ (voucherState[v] = "valid") => (machineState[v] = "active")
        /\ (voucherState[v] \in {"redeemed", "cancelled"}) => (machineState[v] = "terminal")

(***************************************************************************)
(* Initial state: all vouchers start in phantom/unissued state             *)
(***************************************************************************)
Init ==
    /\ voucherState = [v \in Vouchers |-> "phantom"]
    /\ voucherHolder = [v \in Vouchers |-> "none"]
    /\ machineState = [v \in Vouchers |-> "unissued"]

(***************************************************************************)
(* Issue action: voucher moves from phantom to valid state                 *)
(***************************************************************************)
Issue(v, h) ==
    /\ voucherState[v] = "phantom"
    /\ machineState[v] = "unissued"
    /\ h \in Holders
    /\ voucherState' = [voucherState EXCEPT ![v] = "valid"]
    /\ voucherHolder' = [voucherHolder EXCEPT ![v] = h]
    /\ machineState' = [machineState EXCEPT ![v] = "active"]

(***************************************************************************)
(* Transfer action: voucher changes holder while remaining valid           *)
(* This is a stuttering action with respect to voucher state               *)
(***************************************************************************)
Transfer(v, h) ==
    /\ voucherState[v] = "valid"
    /\ machineState[v] = "active"
    /\ h \in Holders
    /\ h # voucherHolder[v]  \* Transfer to a different holder
    /\ voucherState' = voucherState  \* State unchanged (stuttering)
    /\ voucherHolder' = [voucherHolder EXCEPT ![v] = h]
    /\ machineState' = machineState  \* Machine state unchanged

(***************************************************************************)
(* Redeem action: valid voucher is redeemed                                *)
(***************************************************************************)
Redeem(v) ==
    /\ voucherState[v] = "valid"
    /\ machineState[v] = "active"
    /\ voucherState' = [voucherState EXCEPT ![v] = "redeemed"]
    /\ voucherHolder' = voucherHolder  \* Holder remains recorded
    /\ machineState' = [machineState EXCEPT ![v] = "terminal"]

(***************************************************************************)
(* Cancel action: valid voucher is cancelled                               *)
(***************************************************************************)
Cancel(v) ==
    /\ voucherState[v] = "valid"
    /\ machineState[v] = "active"
    /\ voucherState' = [voucherState EXCEPT ![v] = "cancelled"]
    /\ voucherHolder' = voucherHolder  \* Holder remains recorded
    /\ machineState' = [machineState EXCEPT ![v] = "terminal"]

(***************************************************************************)
(* Next-state relation: disjunction of all voucher actions                 *)
(***************************************************************************)
Next ==
    \E v \in Vouchers:
        \/ \E h \in Holders: Issue(v, h)
        \/ \E h \in Holders: Transfer(v, h)
        \/ Redeem(v)
        \/ Cancel(v)

(***************************************************************************)
(* Variables tuple for temporal formulas                                   *)
(***************************************************************************)
vars == <<voucherState, voucherHolder, machineState>>

(***************************************************************************)
(* Fairness condition: weak fairness on all actions                        *)
(***************************************************************************)
Fairness ==
    /\ \A v \in Vouchers:
        /\ \A h \in Holders: WF_vars(Issue(v, h))
        /\ \A h \in Holders: WF_vars(Transfer(v, h))
        /\ WF_vars(Redeem(v))
        /\ WF_vars(Cancel(v))

(***************************************************************************)
(* Temporal specification                                                  *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety invariant: conjunction of type correctness and consistency       *)
(***************************************************************************)
SafetyInvariant == TypeOK /\ Consistency

(***************************************************************************)
(* Liveness property: every issued voucher eventually reaches terminal     *)
(***************************************************************************)
EventuallyTerminal ==
    \A v \in Vouchers:
        (voucherState[v] = "valid") ~> (machineState[v] = "terminal")

(***************************************************************************)
(* Theorem: Under the specification, safety invariant is always preserved  *)
(***************************************************************************)
THEOREM Spec => []SafetyInvariant

(***************************************************************************)
(* Theorem: Under the specification, liveness property holds               *)
(***************************************************************************)
THEOREM Spec => EventuallyTerminal

=============================================================================