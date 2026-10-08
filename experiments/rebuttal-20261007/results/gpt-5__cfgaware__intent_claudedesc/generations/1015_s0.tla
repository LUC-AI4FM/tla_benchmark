------------------------------- MODULE VoucherLifecycle -------------------------------

EXTENDS TLC

(*
  Voucher lifecycle system inspired by RFC 3506.
  Names required by configuration: V, v2, VTypeOK, VConsistent, VSpec
*)

CONSTANTS
  V,   \* Set of voucher identifiers
  v2   \* A distinguished voucher identifier (assumed to be in V)

(*
  Enumerations of voucher and lifecycle states.
*)
VoucherStates == {"phantom", "valid", "redeemed", "cancelled"}
LifecycleStates == {"unstarted", "inprogress", "completed"}

VARIABLES
  vState,   \* [V -> VoucherStates]
  lcState   \* [V -> LifecycleStates]

vars == << vState, lcState >>

(*
  Initial state: all vouchers start as phantom and lifecycle unstarted.
*)
Init ==
  /\ vState = [v \in V |-> "phantom"]
  /\ lcState = [v \in V |-> "unstarted"]

(*
  Actions on a single voucher v \in V.
*)

Issue(v) ==
  /\ v \in V
  /\ vState[v] = "phantom"
  /\ lcState[v] = "unstarted"
  /\ vState' = [vState EXCEPT ![v] = "valid"]
  /\ lcState' = [lcState EXCEPT ![v] = "inprogress"]

Transfer(v) ==
  /\ v \in V
  /\ vState[v] = "valid"
  /\ lcState[v] = "inprogress"
  /\ UNCHANGED vars

Redeem(v) ==
  /\ v \in V
  /\ vState[v] = "valid"
  /\ lcState[v] = "inprogress"
  /\ vState' = [vState EXCEPT ![v] = "redeemed"]
  /\ lcState' = [lcState EXCEPT ![v] = "completed"]

Cancel(v) ==
  /\ v \in V
  /\ vState[v] = "valid"
  /\ lcState[v] = "inprogress"
  /\ vState' = [vState EXCEPT ![v] = "cancelled"]
  /\ lcState' = [lcState EXCEPT ![v] = "completed"]

Next ==
  \E v \in V:
       Issue(v)
    \/ Transfer(v)
    \/ Redeem(v)
    \/ Cancel(v)

(*
  Type correctness and basic constant relation.
*)
VTypeOK ==
  /\ vState \in [V -> VoucherStates]
  /\ lcState \in [V -> LifecycleStates]
  /\ v2 \in V

(*
  Safety invariant: voucher and lifecycle states are consistent.
  - "phantom"   <=> "unstarted"
  - "valid"     <=> "inprogress"
  - {"redeemed","cancelled"} <=> "completed"
*)
VConsistent ==
  \A v \in V:
    /\ (vState[v] = "phantom") <=> (lcState[v] = "unstarted")
    /\ (vState[v] = "valid") <=> (lcState[v] = "inprogress")
    /\ (vState[v] \in {"redeemed","cancelled"}) <=> (lcState[v] = "completed")

(*
  System specification: no liveness or fairness required.
*)
VSpec == Init /\ [][Next]_vars

=============================================================================