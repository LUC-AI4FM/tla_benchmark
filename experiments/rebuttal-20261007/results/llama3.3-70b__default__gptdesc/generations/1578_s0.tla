```
MODULE DequeSpec
EXTENDS Integers, Sequences, Bags

CONSTANTS Addr, Val, NullNode, Node, LeftHat, RightHat, Freelist
VARIABLES mem, leftHat, rightHat, freelist, pc, valBag, localVars

Init ==
  /\ mem = [i \in Addr |-> NullNode]
  /\ leftHat = NullNode
  /\ rightHat = NullNode
  /\ freelist = Seq()
  /\ pc = [i \in Proc |-> "T1"]
  /\ valBag = EmptyBag(Val)
  /\ localVars = [i \in Proc |-> <<>>]

Next ==
  \/ \E i \in Proc :
      IF pc[i] = "T1"
      THEN
        /\ pc' = [pc EXCEPT ![i] = "T2"]
        /\ valBag' = valBag
        /\ localVars' = localVars
        /\ mem' = mem
        /\ leftHat' = leftHat
        /\ rightHat' = rightHat
        /\ freelist' = freelist
      ELSEIF pc[i] = "T2"
      THEN
        /\ pc' = [pc EXCEPT ![i] = "T3"]
        /\ valBag' = valBag
        /\ localVars' = [localVars EXCEPT ![i] = <<Val>>]
        /\ mem' = mem
        /\ leftHat' = leftHat
        /\ rightHat' = rightHat
        /\ freelist' = freelist
      ELSEIF pc[i] = "T3"
      THEN
        /\ pc' = [pc EXCEPT ![i] = "T4"]
        /\ valBag' = valBag \cup {localVars[i][1]}
        /\ localVars' = [localVars EXCEPT ![i] = <<>>]
        /\ mem' = [mem EXCEPT ![leftHat] = Node(localVars[i][1], rightHat)]
        /\ leftHat' = leftHat
        /\ rightHat' = leftHat
        /\ freelist' = freelist
      ELSEIF pc[i] = "T4"
      THEN
        /\ pc' = [pc EXCEPT ![i] = "T5"]
        /\ valBag' = valBag
        /\ localVars' = [localVars EXCEPT ![i] = <<>>]
        /\ mem' = mem
        /\ leftHat' = leftHat
        /\ rightHat' = rightHat
        /\ freelist' = freelist
      ELSEIF pc[i] = "T5"
      THEN
        /\ pc' = [pc EXCEPT ![i] = "T1"]
        /\ valBag' = valBag
        /\ localVars' = [localVars EXCEPT ![i] = <<>>]
        /\ mem' = mem
        /\ leftHat' = leftHat
        /\ rightHat' = rightHat
        /\ freelist' = freelist

Spec ==
  Init /\ [][Next]_<<mem, leftHat, rightHat, freelist, pc, valBag, localVars>>

THEOREM Spec => []<>pc["test"] = "T1"
```