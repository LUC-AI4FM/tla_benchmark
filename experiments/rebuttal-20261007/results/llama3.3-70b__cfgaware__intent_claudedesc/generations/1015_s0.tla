---------------------------- MODULE VoucherLifecycle ----------------------------
EXTENDS Integers, TLC

CONSTANT V

VARIABLE v, v2, lifecycle

v == [v \in V |-> "phantom"]
lifecycle == [l \in V |-> "unstarted"]

TypeOK == (v \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]) /\
         (lifecycle \in [V -> {"unstarted", "in_progress", "completed"}])

VTypeOK == TypeOK

Consistent == \A v \in V :
              (v[v] = "phantom") <=> (lifecycle[v] = "unstarted") /\
              (v[v] = "valid")    <=> (lifecycle[v] = "in_progress") /\
              (v[v] \in {"redeemed", "cancelled"}) <=> (lifecycle[v] = "completed")

VConsistent == Consistent

Issue(v) == /\ v' = [v EXCEPT ![v] = "valid"]
           /\ lifecycle' = [lifecycle EXCEPT ![v] = "in_progress"]
           /\ v2' = v2
           /\ TypeOK

Transfer(v) == /\ v' = v
               /\ lifecycle' = lifecycle
               /\ v2' = v2
               /\ TypeOK

Redeem(v) == /\ v' = [v EXCEPT ![v] = "redeemed"]
             /\ lifecycle' = [lifecycle EXCEPT ![v] = "completed"]
             /\ v2' = v2
             /\ TypeOK

Cancel(v) == /\ v' = [v EXCEPT ![v] = "cancelled"]
            /\ lifecycle' = [lifecycle EXCEPT ![v] = "completed"]
            /\ v2' = v2
            /\ TypeOK

VSpec == /\ TypeOK
         /\ []<>(\E v \in V : Issue(v) \/ Transfer(v) \/ Redeem(v) \/ Cancel(v))
         /\ WF_vars({Issue, Transfer, Redeem, Cancel}, {v, lifecycle, v2})

=============================================================================