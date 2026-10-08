```
MODULE VoucherLifeCycle

EXTENDS Integers, TLC

CONSTANTS VoucherSet, ActionSet
VARIABLES vouchers, state, actions

Init ==
  /\ vouchers = [v \in VoucherSet |-> "phantom"]
  /\ state = [s \in VoucherSet |-> "initial"]
  /\ actions = << >>

Next ==
  /\ IF (\E v \in VoucherSet : vouchers[v] = "phantom")
     THEN /\ vouchers' = [vouchers EXCEPT ![v] = "valid"]
          /\ state' = [state EXCEPT ![v] = "issued"]
          /\ actions' = << "issue" >> @@ actions
     ELSE
       IF (\E v \in VoucherSet : vouchers[v] = "valid")
         THEN
           /\ (\/ (\E v \in VoucherSet : vouchers[v] = "valid"
                    /\ vouchers' = [vouchers EXCEPT ![v] = "redeemed"]
                    /\ state' = [state EXCEPT ![v] = "redeemed"])
                \/ (\E v \in VoucherSet : vouchers[v] = "valid"
                     /\ vouchers' = [vouchers EXCEPT ![v] = "cancelled"]
                     /\ state' = [state EXCEPT ![v] = "cancelled"])
                \/ (\E v \in VoucherSet : vouchers[v] = "valid"
                     /\ vouchers' = vouchers
                     /\ state' = state
                     /\ actions' = << "transfer" >> @@ actions))
           /\ UNCHANGED actions'
       ELSE
         /\ UNCHANGED vouchers'
         /\ UNCHANGED state'
         /\ UNCHANGED actions'

TypeCorrectness ==
  /\ vouchers \in [VoucherSet -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ state \in [VoucherSet -> {"initial", "issued", "redeemed", "cancelled"}]

ConsistencyInvariant ==
  /\ \A v \in VoucherSet :
      IF vouchers[v] = "phantom"
      THEN state[v] = "initial"
      ELSE IF vouchers[v] = "valid"
           THEN state[v] = "issued"
           ELSE IF vouchers[v] = "redeemed"
                THEN state[v] = "redeemed"
                ELSE state[v] = "cancelled"

Spec ==
  /\ Init
  /\ [][Next]_<<vouchers, state, actions>>
  /\ WF_voucher(v \in VoucherSet : vouchers[v] = "valid" /\ vouchers' = [vouchers EXCEPT ![v] = "redeemed"])
  /\ SF_voucher(v \in VoucherSet : vouchers[v] = "valid" /\ vouchers' = [vouchers EXCEPT ![v] = "cancelled"])

THEOREM Spec => [] (TypeCorrectness /\ ConsistencyInvariant)
```