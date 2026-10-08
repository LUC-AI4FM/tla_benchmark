---------------------------- MODULE VoucherLifecycle ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS V
VARIABLES v, v2

v == [v \in V |-> <<<<"not-yet-issued", "not-started">>]

VTypeOK == 
  (\A v \in V : 
    (v[1] \in {"not-yet-issued", "issued", "consumed", "cancelled"}) /\
    (v[2] \in {"not-started", "active", "completed"}))

VConsistent == 
  (\A v \in V : 
    ((v[1] = "not-yet-issued") <=> (v[2] = "not-started")) /\
    ((v[1] = "issued") <=> (v[2] = "active")) /\
    (((v[1] = "consumed") \/ (v[1] = "cancelled")) <=> (v[2] = "completed")))

Issue(v) == 
  v[1] = "not-yet-issued" /\ 
  v' = [v EXCEPT ![1] = "issued", [2] = "active"]

NoOp(v) == 
  v[1] = "issued" /\ 
  v[2] = "active" /\ 
  v' = v

Redeem(v) == 
  v[1] = "issued" /\ 
  v[2] = "active" /\ 
  v' = [v EXCEPT ![1] = "consumed", [2] = "completed"]

Cancel(v) == 
  v[1] = "issued" /\ 
  v[2] = "active" /\ 
  v' = [v EXCEPT ![1] = "cancelled", [2] = "completed"]

VSpec == 
  (VTypeOK /\ (\A v \in V : v[1] = "not-yet-issued")) /\ 
  [][VTypeOK /\ VConsistent /\ 
    (\A v \in V : 
      ((v[1] = "consumed") \/ (v[1] = "cancelled")) /\ (v[2] = "completed") ==> 
        (v' = v))]

=============================================================================