```
MODULE Deque
EXTENDS Integers, Sequences, Bags

CONSTANTS
  Node, Addr, Value, Null

VARIABLES
  mem,
  leftHat,
  rightHat,
  freelist,
  pc,
  valBag,
  localVars

Init ==
  /\ mem = [i \in Addr |-> [node|->Null, next|->Null, prev|->Null]]
  /\ leftHat = Null
  /\ rightHat = Null
  /\ freelist = Seq(Addr)
  /\ pc = [i \in Proc |-> "T1"]
  /\ valBag = EmptyBag(Value)
  /\ localVars = [i \in Proc |-> <<>>]

Next ==
  /\ IF pc["pushLeft"] = "T2"
    THEN
      /\ mem' = [mem EXCEPT ![leftHat].node = Node]
      /\ leftHat' = Head(freelist)
      /\ freelist' = Tail(freelist)
      /\ localVars' = [localVars EXCEPT !["pushLeft"] = <<Node>>]
      /\ pc' = [pc EXCEPT !["pushLeft"] = "T3"]
  ELSE
    /\ IF pc["pushRight"] = "T2"
      THEN
        /\ mem' = [mem EXCEPT ![rightHat].node = Node]
        /\ rightHat' = Head(freelist)
        /\ freelist' = Tail(freelist)
        /\ localVars' = [localVars EXCEPT !["pushRight"] = <<Node>>]
        /\ pc' = [pc EXCEPT !["pushRight"] = "T3"]
  ELSE
    /\ IF pc["popLeft"] = "T2"
      THEN
        /\ mem' = [mem EXCEPT ![leftHat].node = Null]
        /\ leftHat' = if (mem![leftHat].next = Null) then Null else mem![leftHat].next
        /\ localVars' = [localVars EXCEPT !["popLeft"] = <<>>]
        /\ pc' = [pc EXCEPT !["popLeft"] = "T3"]
  ELSE
    /\ IF pc["popRight"] = "T2"
      THEN
        /\ mem' = [mem EXCEPT ![rightHat].node = Null]
        /\ rightHat' = if (mem![rightHat].prev = Null) then Null else mem![rightHat].prev
        /\ localVars' = [localVars EXCEPT !["popRight"] = <<>>]
        /\ pc' = [pc EXCEPT !["popRight"] = "T3"]
  ELSE
    /\ IF pc["test"] = "T2"
      THEN
        /\ valBag' = valBag + localVars[["test"]]
        /\ pc' = [pc EXCEPT !["test"] = "T1"]

Spec ==
  Init /\ [][Next]_<<mem, leftHat, rightHat, freelist, pc, valBag, localVars>>
  /\ WF_vars(pc("pushLeft") = "T3", pc("pushLeft") = "T1")
  /\ WF_vars(pc("pushRight") = "T3", pc("pushRight") = "T1")
  /\ WF_vars(pc("popLeft") = "T3", pc("popLeft") = "T1")
  /\ WF_vars(pc("popRight") = "T3", pc("popRight") = "T1")

THEOREM Spec => []<>(pc["test"] = "T1")
```