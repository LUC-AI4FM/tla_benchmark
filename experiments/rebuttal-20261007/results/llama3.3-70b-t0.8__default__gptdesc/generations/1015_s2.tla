```
MODULE VoucherLifeCycle

EXTENDS Integers, TLC

CONSTANTS VoucherSet, LifeCycleMachine
VARIABLES vouchers, lifeCycleState

Init ==
  /\ vouchers = [v \in VoucherSet |-> "phantom"]
  /\ lifeCycleState = [v \in VoucherSet |-> "initial"]

Next ==
  /\ ( \E v \in VoucherSet :
        \/ ( vouchers[v] = "phantom" 
             /\ vouchers' = [vouchers EXCEPT ![v] = "valid"] )
        \/ ( vouchers[v] = "valid"
             /\ lifeCycleState[v] = "pending"
             /\ vouchers' = [vouchers EXCEPT ![v] = "redeemed"]
             /\ lifeCycleState' = [lifeCycleState EXCEPT ![v] = "complete"] )
        \/ ( vouchers[v] = "valid"
             /\ lifeCycleState[v] = "pending"
             /\ vouchers' = [vouchers EXCEPT ![v] = "cancelled"]
             /\ lifeCycleState' = [lifeCycleState EXCEPT ![v] = "aborted"] )
        \/ ( vouchers[v] = "valid"
             /\ vouchers' = vouchers
             /\ lifeCycleState' = lifeCycleState ) )
  )

TypeCorrectness ==
  /\ vouchers \in [VoucherSet -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ lifeCycleState \in [VoucherSet -> {"initial", "pending", "complete", "aborted"}]

ConsistencyInvariant ==
  /\ \A v \in VoucherSet :
      ( vouchers[v] = "phantom" 
        ==> lifeCycleState[v] = "initial" )
  /\ \A v \in VoucherSet :
      ( vouchers[v] = "valid"
        ==> lifeCycleState[v] = "pending" )
  /\ \A v \in VoucherSet :
      ( vouchers[v] = "redeemed"
        ==> lifeCycleState[v] = "complete" )
  /\ \A v \in VoucherSet :
      ( vouchers[v] = "cancelled"
        ==> lifeCycleState[v] = "aborted" )

Spec ==
  /\ Init
  /\ [][Next]_vouchers,lifeCycleState
  /\ WF_vouchers( \E v \in VoucherSet : vouchers[v] = "phantom" /\ vouchers' = [vouchers EXCEPT ![v] = "valid"] )
  /\ SF_vouchers( \A v \in VoucherSet : vouchers[v] = "valid" 
                   ==> ( lifeCycleState[v] = "pending" 
                         /\ vouchers' = [vouchers EXCEPT ![v] = "redeemed"]
                         /\ lifeCycleState' = [lifeCycleState EXCEPT ![v] = "complete"] ) )

THEOREM Spec => [] (TypeCorrectness /\ ConsistencyInvariant)
```