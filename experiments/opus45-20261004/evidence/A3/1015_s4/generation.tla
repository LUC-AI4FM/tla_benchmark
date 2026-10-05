---------------------------- MODULE VoucherLifeCycle ----------------------------
(***************************************************************************)
(* This specification models the life cycle of vouchers, based on RFC 3506 *)
(* with the tuple component decoupled. Each voucher begins in a "phantom"  *)
(* state before issuance, may become "valid", and can then either be       *)
(* redeemed or cancelled; transfer is allowed as a stuttering action while *)
(* the voucher remains valid.                                              *)
(***************************************************************************)

EXTENDS Naturals, TLC

CONSTANTS Vouchers  \* The set of all possible voucher identifiers

(***************************************************************************)
(* Voucher states based on RFC 3506 life cycle with phantom state added    *)
(***************************************************************************)
VoucherStates == {"phantom", "valid", "redeemed", "cancelled"}

(***************************************************************************)
(* Life cycle machine states                                               *)
(***************************************************************************)
LifeCycleStates == {"pre_issue", "active", "terminal"}

VARIABLES
    voucherState,    \* Function mapping vouchers to their current state
    lifeCycleState,  \* Function mapping vouchers to their life cycle machine state
    owner            \* Function mapping vouchers to their current owner (for transfer)

vars == <<voucherState, lifeCycleState, owner>>

(***************************************************************************)
(* Type correctness invariant                                              *)
(***************************************************************************)
TypeOK ==
    /\ voucherState \in [Vouchers -> VoucherStates]
    /\ lifeCycleState \in [Vouchers -> LifeCycleStates]
    /\ owner \in [Vouchers -> Nat]  \* Owner represented as natural number ID

(***************************************************************************)
(* Consistency invariant relating voucher state to life-cycle machine state*)
(***************************************************************************)
Consistency ==
    \A v \in Vouchers :
        /\ (voucherState[v] = "phantom") => (lifeCycleState[v] = "pre_issue")
        /\ (voucherState[v] = "valid") => (lifeCycleState[v] = "active")
        /\ (voucherState[v] = "redeemed") => (lifeCycleState[v] = "terminal")
        /\ (voucherState[v] = "cancelled") => (lifeCycleState[v] = "terminal")

(***************************************************************************)
(* Initial state predicate                                                 *)
(***************************************************************************)
Init ==
    /\ voucherState = [v \in Vouchers |-> "phantom"]
    /\ lifeCycleState = [v \in Vouchers |-> "pre_issue"]
    /\ owner = [v \in Vouchers |-> 0]  \* No owner initially

(***************************************************************************)
(* Issue action: transition from phantom to valid                          *)
(***************************************************************************)
Issue(v, newOwner) ==
    /\ voucherState[v] = "phantom"
    /\ lifeCycleState[v] = "pre_issue"
    /\ voucherState' = [voucherState EXCEPT ![v] = "valid"]
    /\ lifeCycleState' = [lifeCycleState EXCEPT ![v] = "active"]
    /\ owner' = [owner EXCEPT ![v] = newOwner]

(***************************************************************************)
(* Redeem action: transition from valid to redeemed                        *)
(***************************************************************************)
Redeem(v) ==
    /\ voucherState[v] = "valid"
    /\ lifeCycleState[v] = "active"
    /\ voucherState' = [voucherState EXCEPT ![v] = "redeemed"]
    /\ lifeCycleState' = [lifeCycleState EXCEPT ![v] = "terminal"]
    /\ UNCHANGED owner

(***************************************************************************)
(* Cancel action: transition from valid to cancelled                       *)
(***************************************************************************)
Cancel(v) ==
    /\ voucherState[v] = "valid"
    /\ lifeCycleState[v] = "active"
    /\ voucherState' = [voucherState EXCEPT ![v] = "cancelled"]
    /\ lifeCycleState' = [lifeCycleState EXCEPT ![v] = "terminal"]
    /\ UNCHANGED owner

(***************************************************************************)
(* Transfer action: stuttering action while voucher is valid               *)
(* Changes owner but keeps voucher in valid state                          *)
(***************************************************************************)
Transfer(v, newOwner) ==
    /\ voucherState[v] = "valid"
    /\ lifeCycleState[v] = "active"
    /\ newOwner # owner[v]  \* Transfer to different owner
    /\ owner' = [owner EXCEPT ![v] = newOwner]
    /\ UNCHANGED <<voucherState, lifeCycleState>>

(***************************************************************************)
(* Next-state relation over voucher actions                                *)
(***************************************************************************)
Next ==
    \E v \in Vouchers :
        \/ \E newOwner \in 1..10 : Issue(v, newOwner)
        \/ Redeem(v)
        \/ Cancel(v)
        \/ \E newOwner \in 1..10 : Transfer(v, newOwner)

(***************************************************************************)
(* Temporal specification with fairness                                    *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Safety invariant: conjunction of type correctness and consistency       *)
(***************************************************************************)
SafetyInvariant == TypeOK /\ Consistency

(***************************************************************************)
(* Theorem: Under the specification, safety invariant is always preserved  *)
(***************************************************************************)
THEOREM Spec => []SafetyInvariant

(***************************************************************************)
(* Liveness property: Every phantom voucher can eventually be issued       *)
(***************************************************************************)
EventuallyIssued == 
    \A v \in Vouchers : 
        (voucherState[v] = "phantom") ~> (voucherState[v] # "phantom")

(***************************************************************************)
(* Liveness property: Every valid voucher eventually reaches terminal state*)
(***************************************************************************)
EventuallyTerminal ==
    \A v \in Vouchers :
        (voucherState[v] = "valid") ~> (lifeCycleState[v] = "terminal")

=============================================================================