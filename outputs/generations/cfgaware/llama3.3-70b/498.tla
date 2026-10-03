---------------------------- MODULE MultiSlotConsensus ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Slots, Values
VARIABLE proposed, chosen

Init == (proposed = {} /\ chosen = [s \in Slots |-> {}])

Propose(v) == 
  IF v \in Values /\ v \notin proposed 
  THEN proposed' = proposed \cup {v} 
  ELSE proposed' = proposed
  ENDIF

Choose(s, v) == 
  IF s \in Slots /\ v \in proposed /\ chosen[s] = {} 
  THEN chosen' = [chosen EXCEPT ![s] = {v}] 
  ELSE chosen' = chosen
  ENDIF

Next == (\E v \in Values : Propose(v)) \/ (\E s \in Slots : \E v \in proposed : Choose(s, v))

Spec == Init /\ [][Next]_<<proposed, chosen>>
LiveSpec == Spec /\ WF_vars(Next, <<proposed, chosen>>)
=============================================================================