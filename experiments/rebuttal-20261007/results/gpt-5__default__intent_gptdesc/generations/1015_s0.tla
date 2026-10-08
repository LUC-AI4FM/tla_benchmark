--------------------------- MODULE VoucherLifecycle ---------------------------

EXTENDS TLC

CONSTANT V \* The set of vouchers

(*
Business states:
  "NotYetIssued" | "Issued" | "Consumed" | "Cancelled"
Lifecycle-machine states:
  "NotStarted" | "Active" | "Completed"
*)
BizStates == {"NotYetIssued", "Issued", "Consumed", "Cancelled"}
LCStates  == {"NotStarted", "Active", "Completed"}

VARIABLES biz, lc

vars == << biz, lc >>

Init ==
  /\ biz \in [V -> BizStates]
  /\ lc  \in [V -> LCStates]
  /\ biz = [v \in V |-> "NotYetIssued"]
  /\ lc  = [v \in V |-> "NotStarted"]

Issue(v) ==
  /\ v \in V
  /\ biz[v] = "NotYetIssued"
  /\ lc[v]  = "NotStarted"
  /\ biz'   = [biz EXCEPT ![v] = "Issued"]
  /\ lc'    = [lc  EXCEPT ![v] = "Active"]

Transfer(v) ==
  /\ v \in V
  /\ biz[v] = "Issued"
  /\ lc[v]  = "Active"
  /\ UNCHANGED vars

Redeem(v) ==
  /\ v \in V
  /\ biz[v] = "Issued"
  /\ lc[v]  = "Active"
  /\ biz'   = [biz EXCEPT ![v] = "Consumed"]
  /\ lc'    = [lc  EXCEPT ![v] = "Completed"]

Cancel(v) ==
  /\ v \in V
  /\ biz[v] = "Issued"
  /\ lc[v]  = "Active"
  /\ biz'   = [biz EXCEPT ![v] = "Cancelled"]
  /\ lc'    = [lc  EXCEPT ![v] = "Completed"]

Next ==
  \E v \in V:
       Issue(v)
    \/ Transfer(v)
    \/ Redeem(v)
    \/ Cancel(v)

Spec == Init /\ [][Next]_vars

(******************** Safety invariants ********************)

TypeInv ==
  /\ biz \in [V -> BizStates]
  /\ lc  \in [V -> LCStates]

ConsistencyInv ==
  \A v \in V:
    /\ (biz[v] = "NotYetIssued") <=> (lc[v] = "NotStarted")
    /\ (biz[v] = "Issued")       <=> (lc[v] = "Active")
    /\ (biz[v] \in {"Consumed","Cancelled"}) <=> (lc[v] = "Completed")

Xor(a, b) == (a /\ ~b) \/ (~a /\ b)

TerminalExclusivityInv ==
  \A v \in V:
    (lc[v] = "Completed") => Xor(biz[v] = "Consumed", biz[v] = "Cancelled")

Inv == TypeInv /\ ConsistencyInv /\ TerminalExclusivityInv

(*
Monotonicity/terminal stability across steps:
 - Once completed, both the lifecycle and business state remain terminal and unchanged.
 - Once issued, it never reverts to "NotYetIssued" (and lifecycle never reverts to "NotStarted").
*)
CompletedStable ==
  [](\A v \in V:
       (lc[v] = "Completed")
         => /\ lc'[v] = "Completed"
            /\ biz'[v] = biz[v])

NoRevertFromIssued ==
  [](\A v \in V:
       (biz[v] = "Issued") => biz'[v] # "NotYetIssued")

NoRevertLifecycle ==
  [](\A v \in V:
       (lc[v] = "Active") => lc'[v] # "NotStarted")

Safety == []Inv /\ CompletedStable /\ NoRevertFromIssued /\ NoRevertLifecycle

(******************** Liveness/enablement expectations ********************)

(*
Issuing is possible only from not-yet-issued/not-started, and
redemption or cancellation only from issued/active.
We state both enablement (can happen) and only-from (when they happen).
*)

IssueEnabledWhenNYI ==
  [](\A v \in V:
       (biz[v] = "NotYetIssued" /\ lc[v] = "NotStarted") => Enabled Issue(v))

RedeemOrCancelEnabledWhenActive ==
  [](\A v \in V:
       (biz[v] = "Issued" /\ lc[v] = "Active")
         => (Enabled Redeem(v) \/ Enabled Cancel(v)))

IssueOnlyFromNYI ==
  [](\A v \in V:
       Issue(v) => (biz[v] = "NotYetIssued" /\ lc[v] = "NotStarted"))

RedeemOnlyFromIssuedActive ==
  [](\A v \in V:
       Redeem(v) => (biz[v] = "Issued" /\ lc[v] = "Active"))

CancelOnlyFromIssuedActive ==
  [](\A v \in V:
       Cancel(v) => (biz[v] = "Issued" /\ lc[v] = "Active"))

Liveness == IssueEnabledWhenNYI /\ RedeemOrCancelEnabledWhenActive
OnlyFrom == IssueOnlyFromNYI /\ RedeemOnlyFromIssuedActive /\ CancelOnlyFromIssuedActive

=============================================================================