----------------------------- MODULE VoucherLifeCycle -----------------------------

EXTENDS Naturals

CONSTANTS
  VOUCHERS, \* Nonempty set of voucher identifiers
  TUPLE,    \* Domain of decoupled tuple values (e.g., holder, metadata)
  Undef     \* Distinguished value not in TUPLE, used before issuance

ASSUME VOUCHERS # {}
ASSUME Undef \notin TUPLE

VARIABLES
  lc,   \* Lifecycle machine state for each voucher
  tup   \* Decoupled tuple component for each voucher

LCStates == {"phantom", "valid", "redeemed", "cancelled"}

TypeOK ==
  /\ lc \in [VOUCHERS -> LCStates]
  /\ tup \in [VOUCHERS -> (TUPLE \cup {Undef})]

ConsistencyInv ==
  \A v \in VOUCHERS :
    /\ (lc[v] = "phantom" => tup[v] = Undef)
    /\ (lc[v] = "valid" => tup[v] \in TUPLE)
    /\ (lc[v] \in {"redeemed","cancelled"} => tup[v] \in TUPLE)

Init ==
  /\ lc  = [v \in VOUCHERS |-> "phantom"]
  /\ tup = [v \in VOUCHERS |-> Undef]

Issue(v, t) ==
  /\ v \in VOUCHERS
  /\ t \in TUPLE
  /\ lc[v] = "phantom"
  /\ lc'  = [lc EXCEPT ![v] = "valid"]
  /\ tup' = [tup EXCEPT ![v] = t]

Transfer(v, t) ==
  /\ v \in VOUCHERS
  /\ t \in TUPLE
  /\ lc[v] = "valid"
  /\ lc'  = lc
  /\ tup' = [tup EXCEPT ![v] = t]

Redeem(v) ==
  /\ v \in VOUCHERS
  /\ lc[v] = "valid"
  /\ lc'  = [lc EXCEPT ![v] = "redeemed"]
  /\ tup' = tup

Cancel(v) ==
  /\ v \in VOUCHERS
  /\ lc[v] = "valid"
  /\ lc'  = [lc EXCEPT ![v] = "cancelled"]
  /\ tup' = tup

Next ==
  \/ \E v \in VOUCHERS, t \in TUPLE : Issue(v, t)
  \/ \E v \in VOUCHERS, t \in TUPLE : Transfer(v, t)
  \/ \E v \in VOUCHERS : Redeem(v)
  \/ \E v \in VOUCHERS : Cancel(v)

vars == << lc, tup >>

Spec == Init /\ [][Next]_vars

THEOREM AlwaysTypeAndCons == Spec => [](TypeOK /\ ConsistencyInv)

=============================================================================