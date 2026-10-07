```tla
MODULE SnarkDeque
EXTENDS Integers, TLC

CONSTANTS Address, Val, Dummy, Procs
VARIABLES Mem, freeList, LeftHat, RightHat, rVal, valBag

Init ==
  /\ Mem = [i \in Address |-> [left |-> NULL, right |-> NULL, val |-> NULL]]
  /\ freeList = Address \ {Dummy}
  /\ LeftHat = Dummy
  /\ RightHat = Dummy
  /\ rVal = [p \in Procs |-> NULL]
  /\ valBag = {}

Next ==
  \/ \E p \in Procs :
    /\ rVal[p] = NULL
    /\ ( \E v \in Val : 
        /\ Mem[LeftHat].left = NULL
        /\ DCAS(LeftHat, LeftHat, [left |-> NULL, right |-> Dummy, val |-> v], 
                freeList, LeftHat, [left |-> new, right |-> Dummy, val |-> v])
        /\ freeList' = freeList \ {new}
        /\ rVal' = [rVal EXCEPT ![p] = v]
        /\ valBag' = valBag \cup {v}
      \/ \E v \in Val : 
        /\ Mem[RightHat].right = NULL
        /\ DCAS(RightHat, RightHat, [left |-> Dummy, right |-> NULL, val |-> v], 
                freeList, RightHat, [left |-> Dummy, right |-> new, val |-> v])
        /\ freeList' = freeList \ {new}
        /\ rVal' = [rVal EXCEPT ![p] = v]
        /\ valBag' = valBag \cup {v}
      \/ Mem[LeftHat].left /= NULL
        /\ DCAS(LeftHat, LeftHat, [left |-> old, right |-> Dummy, val |-> v], 
                LeftHat, [left |-> NULL, right |-> Dummy, val |-> v])
        /\ rVal' = [rVal EXCEPT ![p] = v]
        /\ valBag' = valBag \ {v}
      \/ Mem[RightHat].right /= NULL
        /\ DCAS(RightHat, RightHat, [left |-> Dummy, right |-> old, val |-> v], 
                RightHat, [left |-> Dummy, right |-> NULL, val |-> v])
        /\ rVal' = [rVal EXCEPT ![p] = v]
        /\ valBag' = valBag \ {v}
    )
  \/ Mem' = Mem
  /\ freeList' = freeList
  /\ LeftHat' = LeftHat
  /\ RightHat' = RightHat
  /\ rVal' = rVal
  /\ valBag' = valBag

Spec == Init /\ [][Next]_vars

THEOREM Spec => []valBag \subseteq Val
```