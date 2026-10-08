MODULE VoucherLifeCycle
EXTENDS Naturals, Sequences

CONSTANTS Vouchers

VARIABLES state, lcState

\* State constants
CONSTANT PHANTOM, VALID, REDEEMED, CANCELLED
StateSet == {PHANTOM, VALID, REDEEMED, CANCELLED}

Init ==
  /\ state = [v \in Vouchers |-> PHANTOM]
  /\ lcState = [v \in Vouchers |-> PHANTOM]

Issue ==
  \E v \in Vouchers :
    /\ state[v] = PHANTOM
    /\ state' = [state EXCEPT ![v] = VALID]
    /\ lcState' = [lcState EXCEPT ![v] = VALID]

Redeem ==
  \E v \in Vouchers :
    /\ state[v] = VALID
    /\ state' = [state EXCEPT ![v] = REDEEMED]
    /\ lcState' = [lcState EXCEPT ![v] = REDEEMED]

Cancel ==
  \E v \in Vouchers :
    /\ state[v] = VALID
    /\ state' = [state EXCEPT ![v] = CANCELLED]
    /\ lcState' = [lcState EXCEPT ![v] = CANCELLED]

Transfer ==
  \E v \in Vouchers :
    /\ state[v] = VALID
    /\ state' = state
    /\ lcState' = lcState

Next == Issue \/ Redeem \/ Cancel \/ Transfer

TypeOK ==
  /\ state \in [Vouchers -> StateSet]
  /\ lcState \in [Vouchers -> StateSet]

ConsistencyInvariant ==
  /\ state = lcState

Spec == Init /\ [][Next]_<<state, lcState>> /\ TypeOK /\ ConsistencyInvariant
===============================================================================