----------------------------- MODULE VoucherLifecycle -----------------------------

EXTENDS Naturals, TLC

CONSTANTS
  VOUCHERS,   \* Set of voucher identifiers
  HOLDERS,    \* Set of potential holders
  Null        \* Distinguished value denoting absence of a holder

ASSUME Null \notin HOLDERS

VARIABLES
  life,       \* [VOUCHERS -> States]
  owner       \* [VOUCHERS -> HOLDERS \cup {Null}]

States == {"phantom", "valid", "redeemed", "cancelled"}

TypeOK ==
  /\ life \in [VOUCHERS -> States]
  /\ owner \in [VOUCHERS -> (HOLDERS \cup {Null})]

Consistency ==
  \A v \in VOUCHERS :
    IF life[v] = "valid"
      THEN owner[v] \in HOLDERS
      ELSE owner[v] = Null

Init ==
  /\ life = [v \in VOUCHERS |-> "phantom"]
  /\ owner = [v \in VOUCHERS |-> Null]

Issue(v, h) ==
  /\ v \in VOUCHERS
  /\ h \in HOLDERS
  /\ life[v] = "phantom"
  /\ life' = [life EXCEPT ![v] = "valid"]
  /\ owner' = [owner EXCEPT ![v] = h]

Redeem(v) ==
  /\ v \in VOUCHERS
  /\ life[v] = "valid"
  /\ life' = [life EXCEPT ![v] = "redeemed"]
  /\ owner' = [owner EXCEPT ![v] = Null]

Cancel(v) ==
  /\ v \in VOUCHERS
  /\ life[v] = "valid"
  /\ life' = [life EXCEPT ![v] = "cancelled"]
  /\ owner' = [owner EXCEPT ![v] = Null]

Transfer(v, h) ==
  /\ v \in VOUCHERS
  /\ h \in HOLDERS
  /\ life[v] = "valid"
  /\ UNCHANGED life
  /\ owner' = [owner EXCEPT ![v] = h]

Next ==
  \E v \in VOUCHERS :
    \/ \E h \in HOLDERS : Issue(v, h)
    \/ Redeem(v)
    \/ Cancel(v)
    \/ \E h \in HOLDERS : Transfer(v, h)

Vars == << life, owner >>

Spec == Init /\ [][Next]_Vars

THEOREM Spec => [](TypeOK /\ Consistency)
PROOF OBVIOUS

================================================================================