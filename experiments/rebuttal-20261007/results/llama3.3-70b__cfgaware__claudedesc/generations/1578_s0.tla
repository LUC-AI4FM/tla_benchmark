---------------------------- MODULE SnarkDeque ----------------------------
EXTENDS Integers, TLC

CONSTANT Address, Dummy, Val, Procs
VARIABLE Mem, freeList, LeftHat, RightHat, rVal, valBag

defaultInitValue == 0

Mem == [i \in Address |-> [left |-> Dummy, right |-> Dummy, val |-> defaultInitValue]]
freeList == Address \ {Dummy}
LeftHat == Dummy
RightHat == Dummy
rVal == [p \in Procs |-> "empty"]
valBag == {}

DCAS(old1, old2, new1, new2) ==
  /\ Mem[old1.left] = old1
  /\ Mem[old2.right] = old2
  /\ Mem' = [Mem EXCEPT !.left = new1, !.right = new2]

PushRight(p, v) ==
  /\ freeList # {}
  /\ LET node = CHOOSE x \in freeList : TRUE
    IN
      /\ DCAS(<<LeftHat, RightHat>>, <<Mem[LeftHat].right, Mem[RightHat].left>>,
              <<node, LeftHat>>, <<RightHat, node>>)
      /\ freeList' = freeList \ {node}
      /\ rVal' = [rVal EXCEPT !.[p] = v]
      /\ valBag' = IF valBag = {} THEN {v} ELSE valBag \cup {v}

PushLeft(p, v) ==
  /\ freeList # {}
  /\ LET node = CHOOSE x \in freeList : TRUE
    IN
      /\ DCAS(<<RightHat, LeftHat>>, <<Mem[RightHat].left, Mem[LeftHat].right>>,
              <<node, RightHat>>, <<LeftHat, node>>)
      /\ freeList' = freeList \ {node}
      /\ rVal' = [rVal EXCEPT !.[p] = v]
      /\ valBag' = IF valBag = {} THEN {v} ELSE valBag \cup {v}

PopRight(p) ==
  /\ LET node = Mem[RightHat].right
    IN
      /\ DCAS(<<LeftHat, RightHat>>, <<Mem[LeftHat].right, Mem[RightHat].left>>,
              <<node, LeftHat>>, <<Dummy, node>>)
      /\ rVal' = [rVal EXCEPT !.[p] = IF node = Dummy THEN "empty" ELSE Mem[node].val]
      /\ valBag' = IF node = Dummy THEN valBag
                  ELSE IF Mem[node].val \in valBag THEN valBag \ {Mem[node].val}
                  ELSE valBag

PopLeft(p) ==
  /\ LET node = Mem[LeftHat].left
    IN
      /\ DCAS(<<RightHat, LeftHat>>, <<Mem[RightHat].left, Mem[LeftHat].right>>,
              <<node, RightHat>>, <<Dummy, node>>)
      /\ rVal' = [rVal EXCEPT !.[p] = IF node = Dummy THEN "empty" ELSE Mem[node].val]
      /\ valBag' = IF node = Dummy THEN valBag
                  ELSE IF Mem[node].val \in valBag THEN valBag \ {Mem[node].val}
                  ELSE valBag

Next ==
  \/ \E p \in Procs, v \in Val :
        (PushRight(p, v) \/ PushLeft(p, v))
  \/ \E p \in Procs : PopRight(p) \/ PopLeft(p)

Spec == Init /\ [][Next]_vars
=============================================================================