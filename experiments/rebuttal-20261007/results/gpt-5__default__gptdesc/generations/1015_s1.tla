------------------------------ MODULE VoucherLifecycle ------------------------------

EXTENDS Naturals

CONSTANT V \* Set of all vouchers

VARIABLES
  st,         \* Life-cycle machine state per voucher: "phantom", "valid", "redeemed", "cancelled"
  Issued,     \* Set of issued vouchers
  Redeemed,   \* Set of redeemed vouchers
  Cancelled   \* Set of cancelled vouchers

LifeCycle == {"phantom", "valid", "redeemed", "cancelled"}

vars == << st, Issued, Redeemed, Cancelled >>

TypeOK ==
  /\ st \in [V -> LifeCycle]
  /\ Issued \subseteq V
  /\ Redeemed \subseteq V
  /\ Cancelled \subseteq V

PhantomSet  == { v \in V : st[v] = "phantom" }
ValidSet    == { v \in V : st[v] = "valid" }
RedeemedSet == { v \in V : st[v] = "redeemed" }
CancelledSet== { v \in V : st[v] = "cancelled" }

Consistency ==
  /\ Redeemed \subseteq Issued
  /\ Cancelled \subseteq Issued
  /\ Redeemed \cap Cancelled = {}
  /\ PhantomSet   = V \ Issued
  /\ ValidSet     = Issued \ (Redeemed \cup Cancelled)
  /\ RedeemedSet  = Redeemed
  /\ CancelledSet = Cancelled

Init ==
  /\ st = [v \in V |-> "phantom"]
  /\ Issued = {}
  /\ Redeemed = {}
  /\ Cancelled = {}

Issue(v) ==
  /\ v \in V
  /\ st[v] = "phantom"
  /\ st' = [st EXCEPT ![v] = "valid"]
  /\ Issued' = Issued \cup {v}
  /\ Redeemed' = Redeemed
  /\ Cancelled' = Cancelled

Redeem(v) ==
  /\ v \in V
  /\ st[v] = "valid"
  /\ st' = [st EXCEPT ![v] = "redeemed"]
  /\ Issued' = Issued
  /\ Redeemed' = Redeemed \cup {v}
  /\ Cancelled' = Cancelled

Cancel(v) ==
  /\ v \in V
  /\ st[v] = "valid"
  /\ st' = [st EXCEPT ![v] = "cancelled"]
  /\ Issued' = Issued
  /\ Redeemed' = Redeemed
  /\ Cancelled' = Cancelled \cup {v}

\* Transfer is modeled as a stuttering action (no observable state change)
\* and is permitted only while there exists at least one valid voucher.
Transfer ==
  /\ \E v \in V : st[v] = "valid"
  /\ UNCHANGED vars

Next ==
  \/ (\E v \in V : Issue(v))
  \/ (\E v \in V : Redeem(v))
  \/ (\E v \in V : Cancel(v))
  \/ Transfer

Spec ==
  Init /\ [][Next]_vars

THEOREM Spec => [](TypeOK /\ Consistency)

=============================================================================