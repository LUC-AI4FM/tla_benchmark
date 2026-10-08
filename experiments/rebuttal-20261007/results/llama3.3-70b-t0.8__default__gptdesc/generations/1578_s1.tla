```
MODULE DequeSpec
EXTENDS Integers, Sequences, Bags

CONSTANTS Addr, Val, Null

VARIABLES mem, leftHat, rightHat, freelist, 
          pc, local, valBag, testDone

Init ==
  /\ mem = [a \in Addr |-> [node|->Null, next|->Null, prev|->Null]]
  /\ leftHat = Null
  /\ rightHat = Null
  /\ freelist = Seq(Addr)
  /\ pc = [p \in Proc |-> "T1"]
  /\ local = [p \in Proc |-> <<>>]
  /\ valBag = {}
  /\ testDone = {}

Next ==
  \/ \E p \in Proc : 
    /\ pc[p] = "T1"
    /\ (local[p] = <<>>) 
      \* PushLeft(p)
    \/ (local[p] = <<>>) 
      \* PushRight(p)
    \/ (local[p] = <<>>) 
      \* PopLeft(p)
    \/ (local[p] = <<>>) 
      \* PopRight(p)
  \/ \E p \in Proc : 
    /\ pc[p] = "PushLeftDone"
    /\ local[p] = <<>>
    /\ valBag' = valBag
    /\ pc' = [pc EXCEPT ![p] = "T1"]
    /\ local' = [local EXCEPT ![p] = <<>>]
  \/ \E p \in Proc : 
    /\ pc[p] = "PushRightDone"
    /\ local[p] = <<>>
    /\ valBag' = valBag
    /\ pc' = [pc EXCEPT ![p] = "T1"]
    /\ local' = [local EXCEPT ![p] = <<>>]
  \/ \E p \in Proc : 
    /\ pc[p] = "PopLeftDone"
    /\ local[p] = <<>>
    /\ valBag' = valBag
    /\ pc' = [pc EXCEPT ![p] = "T1"]
    /\ local' = [local EXCEPT ![p] = <<>>]
  \/ \E p \in Proc : 
    /\ pc[p] = "PopRightDone"
    /\ local[p] = <<>>
    /\ valBag' = valBag
    /\ pc' = [pc EXCEPT ![p] = "T1"]
    /\ local' = [local EXCEPT ![p] = <<>>]

PushLeft(p) ==
  /\ \E v \in Val, a \in Addr : 
      /\ freelist # <<>>
      /\ a = Head(freelist)
      /\ mem[a] = [node|->v, next|->Null, prev|->Null]
      /\ leftHat' = a
      /\ rightHat' = IF (rightHat = Null) THEN a ELSE rightHat
      /\ freelist' = Tail(freelist)
      /\ valBag' = valBag \union {v}
      /\ pc' = [pc EXCEPT ![p] = "PushLeftDone"]
      /\ local' = [local EXCEPT ![p] = <<>>]
  \/ /\ leftHat # Null
    /\ mem[leftHat] = [node|->v, next|->Null, prev|->lp]
    /\ \E lp \in Addr : 
        /\ mem[lp] = [node|->nv, next|->leftHat, prev|->Null]
        /\ mem' = [mem EXCEPT ![leftHat]|-> [node|->nv, next|->Null, prev|->Null]]
        /\ leftHat' = lp
        /\ rightHat' = IF (rightHat = Null) THEN lp ELSE rightHat
        /\ freelist' = <<lp>> \o freelist
        /\ valBag' = valBag \ {v}
        /\ pc' = [pc EXCEPT ![p] = "PopLeftDone"]
        /\ local' = [local EXCEPT ![p] = <<>>]

PushRight(p) ==
  /\ \E v \in Val, a \in Addr : 
      /\ freelist # <<>>
      /\ a = Head(freelist)
      /\ mem[a] = [node|->v, next|->Null, prev|->Null]
      /\ leftHat' = IF (leftHat = Null) THEN a ELSE leftHat
      /\ rightHat' = a
      /\ freelist' = Tail(freelist)
      /\ valBag' = valBag \union {v}
      /\ pc' = [pc EXCEPT ![p] = "PushRightDone"]
      /\ local' = [local EXCEPT ![p] = <<>>]
  \/ /\ rightHat # Null
    /\ mem[rightHat] = [node|->v, next|->Null, prev|->rp]
    /\ \E rp \in Addr : 
        /\ mem[rp] = [node|->nv, next|->rightHat, prev|->Null]
        /\ mem' = [mem EXCEPT ![rightHat]|-> [node|->nv, next|->Null, prev|->Null]]
        /\ leftHat' = IF (leftHat = Null) THEN rp ELSE leftHat
        /\ rightHat' = rp
        /\ freelist' = <<rp>> \o freelist
        /\ valBag' = valBag \ {v}
        /\ pc' = [pc EXCEPT ![p] = "PopRightDone"]
        /\ local' = [local EXCEPT ![p] = <<>>]

PopLeft(p) ==
  /\ leftHat # Null
  /\ mem[leftHat] = [node|->v, next|->Null, prev|->lp]
  /\ \E lp \in Addr : 
      /\ mem[lp] = [node|->nv, next|->leftHat, prev|->Null]
      /\ mem' = [mem EXCEPT ![leftHat]|-> [node|->nv, next|->Null, prev|->Null]]
      /\ leftHat' = lp
      /\ rightHat' = IF (rightHat = Null) THEN lp ELSE rightHat
      /\ freelist' = <<lp>> \o freelist
      /\ valBag' = valBag \ {v}
      /\ pc' = [pc EXCEPT ![p] = "PopLeftDone"]
      /\ local' = [local EXCEPT ![p] = <<>>]

PopRight(p) ==
  /\ rightHat # Null
  /\ mem[rightHat] = [node|->v, next|->Null, prev|->rp]
  /\ \E rp \in Addr : 
      /\ mem[rp] = [node|->nv, next|->rightHat, prev|->Null]
      /\ mem' = [mem EXCEPT ![rightHat]|-> [node|->nv, next|->Null, prev|->Null]]
      /\ leftHat' = IF (leftHat = Null) THEN rp ELSE leftHat
      /\ rightHat' = rp
      /\ freelist' = <<rp>> \o freelist
      /\ valBag' = valBag \ {v}
      /\ pc' = [pc EXCEPT ![p] = "PopRightDone"]
      /\ local' = [local EXCEPT ![p] = <<>>]

Spec == Init /\ [][Next]_<<mem, leftHat, rightHat, freelist, pc, local, valBag>>
  
Fairness == \A p \in Proc : <>[]pc[p] = "T1"
THEOREM Spec => []<>Fairness
```