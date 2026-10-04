---------------------------- MODULE VoucherLifeCycle ----------------------------
(******************************************************************************)
(* This specification models the life cycle of vouchers, based on RFC 3506,   *)
(* with the tuple component decoupled. Each voucher begins in a newly         *)
(* introduced "phantom" state before issuance, may become "valid", and can    *)
(* then either be redeemed or cancelled; transfer is allowed as a stuttering  *)
(* action while the voucher remains valid.                                    *)
(******************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS
    Vouchers,       \* Set of all voucher identifiers
    Owners          \* Set of all possible owners

VARIABLES
    voucherState,   \* Function mapping voucher to its lifecycle state
    voucherOwner,   \* Function mapping voucher to its current owner
    machineState    \* Function mapping voucher to its state machine state

vars == <<voucherState, voucherOwner, machineState>>

(******************************************************************************)
(* Voucher lifecycle states                                                   *)
(******************************************************************************)
VoucherStates == {"phantom", "valid", "redeemed", "cancelled"}

(******************************************************************************)
(* State machine states corresponding to lifecycle                            *)
(******************************************************************************)
MachineStates == {"unissued", "issued", "terminated"}

(******************************************************************************)
(* Type correctness invariant                                                 *)
(******************************************************************************)
TypeOK ==
    /\ voucherState \in [Vouchers -> VoucherStates]
    /\ voucherOwner \in [Vouchers -> Owners \cup {CHOOSE x : x \notin Owners}]
    /\ machineState \in [Vouchers -> MachineStates]

NoOwner == CHOOSE x : x \notin Owners

(******************************************************************************)
(* Consistency invariant relating voucher state to life-cycle machine state   *)
(******************************************************************************)
Consistency ==
    \A v \in Vouchers :
        /\ (voucherState[v] = "phantom") => (machineState[v] = "unissued")
        /\ (voucherState[v] = "valid") => (machineState[v] = "issued")
        /\ (voucherState[v] = "redeemed") => (machineState[v] = "terminated")
        /\ (voucherState[v] = "cancelled") => (machineState[v] = "terminated")

(******************************************************************************)
(* Initial state: all vouchers start in phantom state                         *)
(******************************************************************************)
Init ==
    /\ voucherState = [v \in Vouchers |-> "phantom"]
    /\ voucherOwner = [v \in Vouchers |-> NoOwner]
    /\ machineState = [v \in Vouchers |-> "unissued"]

(******************************************************************************)
(* Issue action: moves voucher from phantom to valid state                    *)
(******************************************************************************)
Issue(v, owner) ==
    /\ voucherState[v] = "phantom"
    /\ owner \in Owners
    /\ voucherState' = [voucherState EXCEPT ![v] = "valid"]
    /\ voucherOwner' = [voucherOwner EXCEPT ![v] = owner]
    /\ machineState' = [machineState EXCEPT ![v] = "issued"]

(******************************************************************************)
(* Redeem action: moves voucher from valid to redeemed state                  *)
(******************************************************************************)
Redeem(v) ==
    /\ voucherState[v] = "valid"
    /\ voucherState' = [voucherState EXCEPT ![v] = "redeemed"]
    /\ machineState' = [machineState EXCEPT ![v] = "terminated"]
    /\ UNCHANGED voucherOwner

(******************************************************************************)
(* Cancel action: moves voucher from valid to cancelled state                 *)
(******************************************************************************)
Cancel(v) ==
    /\ voucherState[v] = "valid"
    /\ voucherState' = [voucherState EXCEPT ![v] = "cancelled"]
    /\ machineState' = [machineState EXCEPT ![v] = "terminated"]
    /\ UNCHANGED voucherOwner

(******************************************************************************)
(* Transfer action: stuttering action that changes owner while voucher        *)
(* remains valid (state does not change, only ownership)                      *)
(******************************************************************************)
Transfer(v, newOwner) ==
    /\ voucherState[v] = "valid"
    /\ newOwner \in Owners
    /\ newOwner # voucherOwner[v]
    /\ voucherOwner' = [voucherOwner EXCEPT ![v] = newOwner]
    /\ UNCHANGED <<voucherState, machineState>>

(******************************************************************************)
(* Next-state relation: disjunction of all possible actions                   *)
(******************************************************************************)
Next ==
    \E v \in Vouchers :
        \/ \E owner \in Owners : Issue(v, owner)
        \/ Redeem(v)
        \/ Cancel(v)
        \/ \E newOwner \in Owners : Transfer(v, newOwner)

(******************************************************************************)
(* Fairness condition: weak fairness on all voucher actions                   *)
(******************************************************************************)
Fairness ==
    \A v \in Vouchers :
        /\ WF_vars(\E owner \in Owners : Issue(v, owner))
        /\ WF_vars(Redeem(v))
        /\ WF_vars(Cancel(v))

(******************************************************************************)
(* Temporal specification                                                     *)
(******************************************************************************)
Spec == Init /\ [][Next]_vars /\ Fairness

(******************************************************************************)
(* Safety invariant: conjunction of type correctness and consistency          *)
(******************************************************************************)
Safety == TypeOK /\ Consistency

(******************************************************************************)
(* Theorem: Under the specification, Safety is always preserved               *)
(******************************************************************************)
THEOREM Spec => []Safety

(******************************************************************************)
(* Liveness property: every phantom voucher eventually gets issued or         *)
(* the system stutters forever                                                *)
(******************************************************************************)
EventualProgress ==
    \A v \in Vouchers :
        (voucherState[v] = "phantom") ~> (voucherState[v] # "phantom")

(******************************************************************************)
(* Liveness property: every valid voucher eventually terminates               *)
(******************************************************************************)
EventualTermination ==
    \A v \in Vouchers :
        (voucherState[v] = "valid") ~> (machineState[v] = "terminated")

=============================================================================