------------------------------ MODULE VoucherLifecycle ------------------------------
IMPORTING Naturals

CONSTANTS V \* set of voucher identifiers (e.g., ℕ)

VARIABLE v2

\* --- State constants ---------------------------------------------------------
CONSTANT PHANTOM, VALID, REDEEMED, CANCELLED
State == {PHANTOM, VALID, REDEEMED, CANCELLED}

\* --- Type correctness invariant ---------------------------------------------
VTypeOK ==
  /\ v2 \in [V -> State]
  /\ DOMAIN v2 = V

\* --- Consistency invariant (life‑cycle constraints) --------------------------
VConsistent ==
  \A v \in V :
    LET s == v2[v] IN
      \/ (s = PHANTOM)
      \/ (s = VALID)
      \/ (s = REDEEMED)
      \/ (s = CANCELLED)

\* --- Voucher actions ---------------------------------------------------------
Issuance(v) ==
  /\ v \in V
  /\ v2[v] = PHANTOM
  /\ v2' = [v2 EXCEPT ![v] = VALID]

Redemption(v) ==
  /\ v \in V
  /\ v2[v] = VALID
  /\ v2' = [v2 EXCEPT ![v] = REDEEMED]

Cancellation(v) ==
  /\ v \in V
  /\ v2[v] = VALID
  /\ v2' = [v2 EXCEPT ![v] = CANCELLED]

Transfer(v) ==
  /\ v \in V
  /\ v2[v] = VALID
  /\ v2' = v2          \* stuttering action

Next == \/ \E v \in V: Issuance(v)
      \/ \E v \in V: Redemption(v)
      \/ \E v \in V: Cancellation(v)
      \/ \E v \in V: Transfer(v)

\* --- Initialization ---------------------------------------------------------
Init ==
  /\ v2 \in [V -> State]
  /\ DOMAIN v2 = V
  /\ \A v \in V : v2[v] = PHANTOM

\* --- Temporal specification --------------------------------------------------
Spec == Init /\ []Next

VSpec == Spec

\* --- Proof that type correctness and consistency are preserved ----------------
THEOREM TypeConsistencyPreserved ==
  ASSUME Spec
  PROVE [] (VTypeOK /\ VConsistent)

PROOF
  BY Init, Next, VTypeOK, VConsistent
=============================================================================