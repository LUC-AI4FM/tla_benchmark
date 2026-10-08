---------------------------- MODULE ABP_Abstract ----------------------------

CONSTANT Data

VARIABLES sVal, rVal, sBit, rBit, aBit

Bits == {0, 1}
Flip(b) == IF b = 0 THEN 1 ELSE 0

Vars == << sVal, rVal, sBit, rBit, aBit >>

TypeInv ==
  /\ sBit \in Bits
  /\ rBit \in Bits
  /\ aBit \in Bits
  /\ sVal \in Data
  /\ rVal \in Data

Init ==
  /\ sVal \in Data
  /\ rVal \in Data
  /\ sBit \in Bits
  /\ rBit = sBit
  /\ aBit = sBit

SendNew ==
  /\ aBit = sBit
  /\ sVal' \in Data
  /\ sBit' = Flip(sBit)
  /\ UNCHANGED << rVal, rBit, aBit >>

Receive ==
  /\ rBit /= sBit
  /\ rVal' = sVal
  /\ rBit' = sBit
  /\ UNCHANGED << sVal, sBit, aBit >>

Acknowledge ==
  /\ aBit /= rBit
  /\ aBit' = rBit
  /\ UNCHANGED << sVal, sBit, rVal, rBit >>

Next == SendNew \/ Receive \/ Acknowledge

ABCSpec ==
  Init /\ [][Next]_Vars
       /\ WF_Vars(Receive)
       /\ WF_Vars(Acknowledge)

=============================================================================