```tla
MODULE DequeSpec
EXTENDS Integers, Sequences, TLC

CONSTANTS Addr, Val, NullNode, NullVal, NumProcs
VARIABLES mem, leftHat, rightHat, freelist, 
          pc, localVars, valBag, testDone

Init ==
  /\ mem = [i \in Addr |-> <<NullNode, NullVal>>]
  /\ leftHat = NullNode
  /\ rightHat = NullNode
  /\ freelist = Seq(Addr)
  /\ pc = [i \in 1..NumProcs |-> "T1"]
  /\ localVars = [i \in 1..NumProcs |-> <<NullNode, NullVal>>]
  /\ valBag = {}
  /\ testDone = FALSE

PushLeft ==
  /\ pc' = [pc EXCEPT ![1] = "T2"]
  /\ localVars' = [localVars EXCEPT ![1] = <<leftHat, Val>>]
  /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, testDone>>

PushRight ==
  /\ pc' = [pc EXCEPT ![2] = "T3"]
  /\ localVars' = [localVars EXCEPT ![2] = <<rightHat, Val>>]
  /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, testDone>>

PopLeft ==
  /\ pc' = [pc EXCEPT ![1] = "T4"]
  /\ localVars' = [localVars EXCEPT ![1] = <<leftHat, NullVal>>]
  /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, testDone>>

PopRight ==
  /\ pc' = [pc EXCEPT ![2] = "T5"]
  /\ localVars' = [localVars EXCEPT ![2] = <<rightHat, NullVal>>]
  /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, testDone>>

TestProcess ==
  \/ PushLeft
  \/ PushRight
  \/ PopLeft
  \/ PopRight

Next ==
  TestProcess
  /\ pc' = [pc EXCEPT ![i] = IF pc[i] = "T2" THEN "T1" ELSE pc[i]]

Spec ==
  Init /\ [][Next]_<<mem, leftHat, rightHat, freelist, pc, localVars, valBag, testDone>>
  /\ WF_vars(Next, pc)

THEOREM Spec => []<>pc[1] = "T1"
```