---------------------------- MODULE DequeSpec ----------------------------
EXTENDS Integers, TLC, Sequences

CONSTANT Null, Val, Addresses
VARIABLE mem, leftHat, rightHat, freelist, pc, localVars, valBag

defaultInitValue == <<>>, <<>>, <<>>, <<>>, <<1>> 

Spec == 
  /\ Init
  /\ [][Next]_<<mem, leftHat, rightHat, freelist, pc, localVars, valBag>>
  /\ WF_vars(Next, <<mem, leftHat, rightHat, freelist, pc, localVars, valBag>>)
  /\ SF_vars(Next, <<mem, leftHat, rightHat, freelist, pc, localVars, valBag>>)

Init == 
  /\ mem = [i \in Addresses |-> [node|->Null, next|->Null]]
  /\ leftHat = Null
  /\ rightHat = Null
  /\ freelist = Seq(Addresses)
  /\ pc = [p \in Proc |-> "T1"]
  /\ localVars = [p \in Proc |-> <<>>]
  /\ valBag = {}

Next == 
  \/ PushLeft
  \/ PushRight
  \/ PopLeft
  \/ PopRight

PushLeft == 
  /\ pc["p"] = "T1"
  /\ localVars' = [localVars EXCEPT ![p] = <<Val>>]
  /\ pc' = [pc EXCEPT ![p] = "T2"]
  /\ valBag' = valBag \cup {Val}

PushRight == 
  /\ pc["p"] = "T1"
  /\ localVars' = [localVars EXCEPT ![p] = <<Val>>]
  /\ pc' = [pc EXCEPT ![p] = "T3"]
  /\ valBag' = valBag \cup {Val}

PopLeft == 
  /\ pc["p"] = "T1"
  /\ localVars' = [localVars EXCEPT ![p] = <<>>]
  /\ pc' = [pc EXCEPT ![p] = "T4"]
  /\ valBag' = valBag \ {Val}

PopRight == 
  /\ pc["p"] = "T1"
  /\ localVars' = [localVars EXCEPT ![p] = <<>>]
  /\ pc' = [pc EXCEPT ![p] = "T5"]
  /\ valBag' = valBag \ {Val}

WF_vars(Next, vars) == 
  /\ []<<Next>>_vars
  /\ <><<Next>>_vars

SF_vars(Next, vars) == 
  <>[]<<Next>>_vars

THEOREM Spec => []<>pc["p"] = "T1"
=============================================================================