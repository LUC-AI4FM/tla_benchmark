----------------------------- MODULE VoucherLifecycle -----------------------------

EXTENDS Naturals

CONSTANTS Vouchers

States == {"phantom", "valid", "redeemed", "cancelled"}
LCStates == {"before", "usable", "after"}

VARIABLES vs, lc

TypeOK ==
  /\ vs \in [Vouchers -> States]
  /\ lc \in [Vouchers -> LCStates]

Init ==
  /\ vs = [v \in Vouchers |-> "phantom"]
  /\ lc = [v \in Vouchers |-> "before"]
  /\ TypeOK

Issue(v) ==
  /\ v \in Vouchers
  /\ vs[v] = "phantom"
  /\ vs' = [vs EXCEPT ![v] = "valid"]
  /\ lc' = [lc EXCEPT ![v] = "usable"]

Redeem(v) ==
  /\ v \in Vouchers
  /\ vs[v] = "valid"
  /\ vs' = [vs EXCEPT ![v] = "redeemed"]
  /\ lc' = [lc EXCEPT ![v] = "after"]

Cancel(v) ==
  /\ v \in Vouchers
  /\ vs[v] = "valid"
  /\ vs' = [vs EXCEPT ![v] = "cancelled"]
  /\ lc' = [lc EXCEPT ![v] = "after"]

\* Transfer is modeled as an enabled stuttering action while valid.
Transfer(v) ==
  /\ v \in Vouchers
  /\ vs[v] = "valid"
  /\ vs' = vs
  /\ lc' = lc

Next ==
  \E v \in Vouchers:
      Issue(v) \/ Redeem(v) \/ Cancel(v) \/ Transfer(v)

Consistency ==
  \A v \in Vouchers:
    /\ (vs[v] = "phantom") <=> (lc[v] = "before")
    /\ (vs[v] = "valid") <=> (lc[v] = "usable")
    /\ (vs[v] \in {"redeemed", "cancelled"}) <=> (lc[v] = "after")

vars == << vs, lc >>

Spec == Init /\ [][Next]_vars

THEOREM Spec => [](TypeOK /\ Consistency)

=============================================================================