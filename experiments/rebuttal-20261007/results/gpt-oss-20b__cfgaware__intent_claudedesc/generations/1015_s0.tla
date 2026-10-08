------------------------------ MODULE VoucherLifecycle ------------------------------
EXTENDS Naturals, TLC

CONSTANTS V, PHANTOM, VALID, REDEEMED, CANCELLED

VARIABLE v2

(* --------------------------------------------------------------------------- *)
(* Type checking predicate: ensures that every voucher in V has a state and
   the state is one of the allowed values. *)
VTypeOK == \A v \in V : (v \in DOMAIN v2) /\ (v2[v] \in {PHANTOM, VALID, REDEEMED, CANCELLED})

(* --------------------------------------------------------------------------- *)
(* Consistency invariant: voucher states correspond to lifecycle stages.
   Since we do not model a separate lifecycle machine state, this simply
   requires that the state is one of the allowed values. *)
VConsistent == \A v \in V :
  CASE
    v2[v] = PHANTOM -> TRUE
    v2[v] = VALID   -> TRUE
    v2[v] = REDEEMED \/ v2[v] = CANCELLED -> TRUE
  END

(* --------------------------------------------------------------------------- *)
(* Initial state: all vouchers are in the phantom (pre‑issued) state. *)
Init == v2 = [v \in V |-> PHANTOM]

(* --------------------------------------------------------------------------- *)
(* Transition actions for a single voucher. *)
Issue(v) ==
  /\ v \in V
  /\ v2[v] = PHANTOM
  /\ v2' = [v2 EXCEPT ![v] = VALID]

Transfer(v) ==
  /\ v \in V
  /\ v2[v] = VALID
  /\ v2' = v2

Redeem(v) ==
  /\ v \in V
  /\ v2[v] = VALID
  /\ v2' = [v2 EXCEPT ![v] = REDEEMED]

Cancel(v) ==
  /\ v \in V
  /\ v2[v] = VALID
  /\ v2' = [v2 EXCEPT ![v] = CANCELLED]

(* --------------------------------------------------------------------------- *)
(* Next action: exactly one voucher may change state in a step. *)
Next == \E v \in V : Issue(v) \/ Transfer(v) \/ Redeem(v) \/ Cancel(v)

(* --------------------------------------------------------------------------- *)
(* The complete specification. *)
VSpec == Init /\ [][Next]_v2 /\ VTypeOK /\ VConsistent

=============================================================================