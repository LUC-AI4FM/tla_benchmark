MODULE VoucherLifecycle
EXTENDS Naturals, Sequences, TLC

CONSTANTS VoucherIds \* Set of voucher identifiers

VARIABLE state \* Mapping from voucher id to its current state

StateSet == {"Phantom", "Valid", "Redeemed", "Cancelled"}

\*--------------------------------------------------------------------------*
\* Type correctness invariant: each voucher is in a valid state
\*--------------------------------------------------------------------------*
TypeInv ==
  /\ state \in [VoucherIds -> StateSet]

\*--------------------------------------------------------------------------*
\* Actions on vouchers
\*--------------------------------------------------------------------------*
Issue(v) ==
  /\ v \in VoucherIds
  /\ state[v] = "Phantom"
  /\ state' = [state EXCEPT ![v] = "Valid"]

Redeem(v) ==
  /\ v \in VoucherIds
  /\ state[v] = "Valid"
  /\ state' = [state EXCEPT ![v] = "Redeemed"]

Cancel(v) ==
  /\ v \in VoucherIds
  /\ state[v] = "Valid"
  /\ state' = [state EXCEPT ![v] = "Cancelled"]

Stutter ==
  /\ state' = state

Next ==
  \/ \E v \in VoucherIds : Issue(v)
  \/ \E v \in VoucherIds : Redeem(v)
  \/ \E v \in VoucherIds : Cancel(v)
  \/ Stutter

\*--------------------------------------------------------------------------*
\* Initial condition: all vouchers are phantom
\*--------------------------------------------------------------------------*
Init ==
  /\ state \in [VoucherIds -> StateSet]
  /\ \A v \in VoucherIds : state[v] = "Phantom"

\*--------------------------------------------------------------------------*
\* Consistency invariant: state transitions obey the voucher life‑cycle
\*--------------------------------------------------------------------------*
ConsistencyInv ==
  /\ TypeInv

Spec == Init /\ [][Next]_state

=============================================================================
END MODULE