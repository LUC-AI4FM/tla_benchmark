---------------------------- MODULE VoucherLifeCycle ----------------------------
(******************************************************************************)
(* This specification models the life cycle of vouchers, based on RFC 3506,  *)
(* with the tuple component decoupled. Each voucher begins in a "phantom"    *)
(* state before issuance, may become "valid", and can then either be         *)
(* redeemed or cancelled; transfer is allowed as a stuttering action while   *)
(* the voucher remains valid.                                                *)
(******************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS
    Vouchers,       \* Set of all voucher identifiers
    Owners          \* Set of all possible owners

VARIABLES
    voucherState,   \* Function mapping voucher to its lifecycle state
    voucherOwner,   \* Function mapping voucher to its current owner
    machineState    \* Function mapping voucher to its lifecycle machine state

vars == <<voucherState, voucherOwner, machineState>>

(******************************************************************************)
(* Voucher lifecycle states                                                   *)
(******************************************************************************)
VoucherStates == {"phantom", "valid", "redeemed", "cancelled"}

(******************************************************************************)
(* Lifecycle machine states (tracking the phase of the voucher)              *)
(******************************************************************************)
MachineStates == {"pre_issue", "active", "terminal"}

(******************************************************************************)
(* Type correctness invariant                                                 *)
(******************************************************************************)
TypeOK ==
    /\ voucherState \in [Vouchers -> VoucherStates]
    /\ voucherOwner \in [Vouchers -> Owners \cup {CHOOSE x : x \notin Owners}]
    /\ machineState \in [Vouchers -> MachineStates]

(******************************************************************************)
(* No owner constant (representing unassigned)                                *)
(******************************************************************************)
NoOwner == CHOOSE x : x \notin Owners

(******************************************************************************)
(* Consistency invariant: voucher state must be consistent with machine state*)
(******************************************************************************)
Consistency ==
    \A v \in Vouchers:
        /\ (voucherState[v] = "phantom") => (machineState[v] = "pre_issue")
        /\ (voucherState[v] = "valid") => (machineState[v] = "active")
        /\ (voucherState[v] \in {"redeemed", "cancelled"}) => 
           (machineState[v] = "terminal")

(******************************************************************************)
(* Initial state: all vouchers start in phantom state                         *)
(******************************************************************************)
Init ==
    /\ voucherState = [v \in Vouchers |-> "phantom"]
    /\ voucherOwner = [v \in Vouchers |-> NoOwner]
    /\ machineState = [v \in Vouchers |-> "pre_issue"]

(******************************************************************************)
(* Issue action: move voucher from phantom to valid                           *)
(******************************************************************************)
Issue(v, owner) ==
    /\ voucherState[v] = "phantom"
    /\ machineState[v] = "pre_issue"
    /\ owner \in Owners
    /\ voucherState' = [voucherState EXCEPT ![v] = "valid"]
    /\ voucherOwner' = [voucherOwner EXCEPT ![v] = owner]
    /\ machineState' = [machineState EXCEPT ![v] = "active"]

(******************************************************************************)
(* Transfer action: transfer ownership while voucher is valid                 *)
(* This is a stuttering action with respect to voucher state                  *)
(******************************************************************************)
Transfer(v, newOwner) ==
    /\ voucherState[v] = "valid"
    /\ machineState[v] = "active"
    /\ newOwner \in Owners
    /\ newOwner # voucherOwner[v]
    /\ voucherState' = voucherState
    /\ voucherOwner' = [voucherOwner EXCEPT ![v] = newOwner]
    /\ machineState' = machineState

(******************************************************************************)
(* Redeem action: move voucher from valid to redeemed                         *)
(******************************************************************************)
Redeem(v) ==
    /\ voucherState[v] = "valid"
    /\ machineState[v] = "active"
    /\ voucherState' = [voucherState EXCEPT ![v] = "redeemed"]
    /\ voucherOwner' = voucherOwner
    /\ machineState' = [machineState EXCEPT ![v] = "terminal"]

(******************************************************************************)
(* Cancel action: move voucher from valid to cancelled                        *)
(******************************************************************************)
Cancel(v) ==
    /\ voucherState[v] = "valid"
    /\ machineState[v] = "active"
    /\ voucherState' = [voucherState EXCEPT ![v] = "cancelled"]
    /\ voucherOwner' = voucherOwner
    /\ machineState' = [machineState EXCEPT ![v] = "terminal"]

(******************************************************************************)
(* Next state relation: disjunction of all possible actions                   *)
(******************************************************************************)
Next ==
    \E v \in Vouchers:
        \/ \E owner \in Owners: Issue(v, owner)
        \/ \E newOwner \in Owners: Transfer(v, newOwner)
        \/ Redeem(v)
        \/ Cancel(v)

(******************************************************************************)
(* Fairness: weak fairness on all voucher actions                             *)
(******************************************************************************)
Fairness ==
    \A v \in Vouchers:
        /\ WF_vars(\E owner \in Owners: Issue(v, owner))
        /\ WF_vars(Redeem(v))
        /\ WF_vars(Cancel(v))

(******************************************************************************)
(* Temporal specification                                                      *)
(******************************************************************************)
Spec == Init /\ [][Next]_vars /\ Fairness

(******************************************************************************)
(* Safety invariant: TypeOK and Consistency are always preserved              *)
(******************************************************************************)
SafetyInvariant == TypeOK /\ Consistency

(******************************************************************************)
(* Liveness property: every phantom voucher eventually becomes non-phantom    *)
(******************************************************************************)
EventuallyIssued ==
    \A v \in Vouchers:
        (voucherState[v] = "phantom") ~> (voucherState[v] # "phantom")

(******************************************************************************)
(* Liveness property: every valid voucher eventually reaches terminal state   *)
(******************************************************************************)
EventuallyTerminal ==
    \A v \in Vouchers:
        (voucherState[v] = "valid") ~> (voucherState[v] \in {"redeemed", "cancelled"})

(******************************************************************************)
(* Theorem: Spec implies safety invariant is always true                      *)
(******************************************************************************)
THEOREM Spec => []SafetyInvariant

=============================================================================