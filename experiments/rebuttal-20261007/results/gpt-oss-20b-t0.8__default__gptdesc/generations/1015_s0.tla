```
------------------------------- MODULE VoucherLifecycle -------------------------------
EXTENDS Naturals, TLC

CONSTANTS
    Vouchers,
    Phantom,
    Valid,
    Redeemed,
    Cancelled

StateSet == {Phantom, Valid, Redeemed, Cancelled}

VARIABLE voucherState

(* -------------------------------------------------------------------------- *)
(*  Type correctness and consistency invariant                                 *)

TypeCorrectness ==
    /\ voucherState \in [Vouchers -> StateSet]

Consistency ==
    TypeCorrectness

SafetyInvariant ==
    TypeCorrectness

(* -------------------------------------------------------------------------- *)
(*  Initialization                                                             *)

Init ==
    /\ voucherState \in [Vouchers -> StateSet]
    /\ \A v \in Vouchers : voucherState[v] = Phantom

(* -------------------------------------------------------------------------- *)
(*  Actions                                                                    *)

Issue(v) ==
    /\ v \in Vouchers
    /\ voucherState[v] = Phantom
    /\ voucherState' = [voucherState EXCEPT ![v] = Valid]

Redeem(v) ==
    /\ v \in Vouchers
    /\ voucherState[v] = Valid
    /\ voucherState' = [voucherState EXCEPT ![v] = Redeemed]

Cancel(v) ==
    /\ v \in Vouchers
    /\ voucherState[v] = Valid
    /\ voucherState' = [voucherState EXCEPT ![v] = Cancelled]

Transfer(v) ==
    /\ v \in Vouchers
    /\ voucherState[v] = Valid
    /\ voucherState' = voucherState   (* stuttering action *)

Next == Issue(v) \/ Redeem(v) \/ Cancel(v) \/ Transfer(v)

(* -------------------------------------------------------------------------- *)
(*  Temporal specification                                                     *)

Spec ==
    Init
    /\ [][Next]_voucherState
    /\ SafetyInvariant

END MODULE
```