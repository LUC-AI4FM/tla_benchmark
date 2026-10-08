---- MODULE AltBit ----
EXTENDS Naturals

CONSTANTS DataVal

VARIABLES sb, rb, sData, rData

vars == {sb, rb, sData, rData}

Init ==
  sb = 0 /\ 
  rb = 0 /\
  sData ∈ DataVal /\
  rData ∈ DataVal

TypeInv ==
  sb ∈ {0,1} /\ 
  rb ∈ {0,1} /\
  sData ∈ DataVal /\
  rData ∈ DataVal

SenderSend == 
  sb = rb /\ 
  sData' ∈ DataVal /\ 
  sb' = 1 - sb /\ 
  rData' = rData

ReceiverAccept ==
  sb # rb /\ 
  sb' = sb /\ 
  rb' = 1 - rb /\
  rData' = sData /\ 
  sData' = sData

Next == SenderSend \/ ReceiverAccept

FairMsg == WF/[] ReceiverAccept
FairAck == WF/[] SenderSend

Spec == Init /\ [][Next]_vars /\ FairMsg /\ FairAck

SafetyInvariant == TypeInv

LivenessProperty == []<> (sb # rb)

THEOREM Safety ==
  Spec => SafetyInvariant

THEOREM Liveness ==
  Spec => LivenessProperty
---- END MODULE ----