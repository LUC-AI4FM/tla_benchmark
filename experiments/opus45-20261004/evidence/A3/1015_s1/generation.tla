---------------------------- MODULE VoucherLifeCycle ----------------------------
(***************************************************************************)
(* This specification models the life cycle of vouchers, based on RFC 3506 *)
(* with the tuple component decoupled. Each voucher begins in a "phantom"  *)
(* state before issuance, may become "valid", and can then either be       *)
(* redeemed or cancelled; transfer is allowed as a stuttering action while *)
(* the voucher remains valid.                                               *)
(***************************************************************************)

EXTENDS Naturals, TLC

CONSTANTS Vouchers  \* The set of all possible vouchers

(***************************************************************************)
(* Voucher states representing the life cycle                              *)
(***************************************************************************)
VoucherStates == {"phantom", "valid", "redeemed", "cancelled"}

(***************************************************************************)
(* Life cycle machine states                                               *)
(***************************************************************************)
LifeCycleStates == {"unissued", "active", "terminated"}

VARIABLES
    voucherState,    \* Function mapping voucher to its current state
    lifeCycleState,  \* Function mapping voucher to its life cycle machine state
    owner            \* Function mapping voucher to its current owner (for transfer)

vars == <<voucherState, lifeCycleState, owner>>

(***************************************************************************)
(* Type correctness invariant                                              *)
(***************************************************************************)
TypeOK ==
    /\ voucherState \in [Vouchers -> VoucherStates]
    /\ lifeCycleState \in [Vouchers -> LifeCycleStates]
    /\ owner \in [Vouchers -> Nat]

(***************************************************************************)
(* Consistency invariant relating voucher state to life-cycle machine state*)
(***************************************************************************)
Consistency ==
    \A v \in Vouchers :
        /\ (voucherState[v] = "phantom") => (lifeCycleState[v] = "unissued")
        /\ (voucherState[v] = "valid") => (lifeCycleState[v] = "active")
        /\ (voucherState[v] = "redeemed") => (lifeCycleState[v] = "terminated")
        /\ (voucherState[v] = "cancelled") => (lifeCycleState[v] = "terminated")

(***************************************************************************)
(* Initial state: all vouchers start in phantom state                      *)
(***************************************************************************)
Init ==
    /\ voucherState = [v \in Vouchers |-> "phantom"]
    /\ lifeCycleState = [v \in Vouchers |-> "unissued"]
    /\ owner = [v \in Vouchers |-> 0]

(***************************************************************************)
(* Issue action: voucher transitions from phantom to valid                 *)
(***************************************************************************)
Issue(v) ==
    /\ voucherState[v] = "phantom"
    /\ voucherState' = [voucherState EXCEPT ![v] = "valid"]
    /\ lifeCycleState' = [lifeCycleState EXCEPT ![v] = "active"]
    /\ owner' = [owner EXCEPT ![v] = 1]  \* Assign to initial owner

(***************************************************************************)
(* Transfer action: stuttering action while voucher is valid               *)
(* Changes owner but not voucher state                                     *)
(***************************************************************************)
Transfer(v) ==
    /\ voucherState[v] = "valid"
    /\ owner' = [owner EXCEPT ![v] = owner[v] + 1]  \* Transfer to new owner
    /\ UNCHANGED <<voucherState, lifeCycleState>>

(***************************************************************************)
(* Redeem action: voucher transitions from valid to redeemed               *)
(***************************************************************************)
Redeem(v) ==
    /\ voucherState[v] = "valid"
    /\ voucherState' = [voucherState EXCEPT ![v] = "redeemed"]
    /\ lifeCycleState' = [lifeCycleState EXCEPT ![v] = "terminated"]
    /\ UNCHANGED owner

(***************************************************************************)
(* Cancel action: voucher transitions from valid to cancelled              *)
(***************************************************************************)
Cancel(v) ==
    /\ voucherState[v] = "valid"
    /\ voucherState' = [voucherState EXCEPT ![v] = "cancelled"]
    /\ lifeCycleState' = [lifeCycleState EXCEPT ![v] = "terminated"]
    /\ UNCHANGED owner

(***************************************************************************)
(* Next state relation: any voucher can take any applicable action         *)
(***************************************************************************)
Next ==
    \E v \in Vouchers :
        \/ Issue(v)
        \/ Transfer(v)
        \/ Redeem(v)
        \/ Cancel(v)

(***************************************************************************)
(* Fairness conditions                                                     *)
(***************************************************************************)
Fairness ==
    \A v \in Vouchers :
        /\ WF_vars(Issue(v))
        /\ WF_vars(Redeem(v) \/ Cancel(v))

(***************************************************************************)
(* Temporal specification                                                  *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety invariant: TypeOK and Consistency are always preserved           *)
(***************************************************************************)
SafetyInvariant == TypeOK /\ Consistency

(***************************************************************************)
(* Liveness property: every phantom voucher eventually becomes valid       *)
(***************************************************************************)
EventuallyIssued ==
    \A v \in Vouchers : (voucherState[v] = "phantom") ~> (voucherState[v] = "valid")

(***************************************************************************)
(* Liveness property: every valid voucher eventually terminates            *)
(***************************************************************************)
EventuallyTerminated ==
    \A v \in Vouchers : 
        (voucherState[v] = "valid") ~> 
        (voucherState[v] \in {"redeemed", "cancelled"})

(***************************************************************************)
(* Theorem: Spec implies the safety invariant is always preserved          *)
(***************************************************************************)
THEOREM Spec => []SafetyInvariant

=============================================================================