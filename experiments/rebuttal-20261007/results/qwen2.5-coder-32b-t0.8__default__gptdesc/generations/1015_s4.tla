```tla
---- MODULE VoucherLifecycle ----

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Vouchers

VoucherState == {"phantom", "valid", "redeemed", "cancelled"}

VoucherTypeOK(v) == v \in Vouchers

StateTypeOK(state) == \A v \in Vouchers: state[v] \in VoucherState

Init == /\ State = [v \in Vouchers |-> "phantom"]

Next ==
  \/ \E v \in Vouchers:
      /\ State'[v] = "valid"
      /\ \A w \in Vouchers \ {v}: State'[w] = State[w]
  \/ \E v \in Vouchers:
      /\ State[v] = "valid"
      /\ State'[v] = "redeemed"
      /\ \A w \in Vouchers \ {v}: State'[w] = State[w]
  \/ \E v \in Vouchers:
      /\ State[v] = "valid"
      /\ State'[v] = "cancelled"
      /\ \A w \in Vouchers \ {v}: State'[w] = State[w]
  \/ \E v \in Vouchers, newState \in {"valid"}:
      /\ State[v] = "valid"
      /\ State'[v] = newState
      /\ \A w \in Vouchers \ {v}: State'[w] = State[w]

Consistency ==
  /\ StateTypeOK(State)

Spec == 
  /\ Init
  /\ [][Next]_<<State>>
  /\ WF_next(<<State>>)

---- END MODULE ----
```