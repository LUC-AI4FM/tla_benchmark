MODULE SnarkDeque
EXTENDS Naturals, Sequences, TLC

CONSTANTS Address, Val, Procs, Dummy, NULL

(* Type definitions *)
NodeAddr == Address \ {Dummy}
MemType == [left : Address, right : Address, value : Val \/ {"dummy"}]

VARIABLE Mem, freeList, LeftHat, RightHat, rVal, valBag

vars == <<Mem, freeList, LeftHat, RightHat, rVal, valBag>>

(* Initial state *)
Init ==
  /\ Mem = [a \in Address |-> IF a = Dummy THEN
        [left |-> Dummy, right |-> Dummy, value |-> "dummy"]
      ELSE
        [left |-> NULL, right |-> NULL, value |-> NULL]]
  /\ freeList = NodeAddr
  /\ LeftHat = Dummy
  /\ RightHat = Dummy
  /\ rVal = [p \in Procs |-> "none"]
  /\ valBag = [v \in Val |-> 0]

(* Push right operation *)
PushRight(p, v) ==
  \E n \in freeList :
    LET oldLast == Mem[Dummy].left
        newMem ==
          IF oldLast = Dummy THEN
            [Mem EXCEPT ![n] = [left |-> Dummy, right |-> Dummy, value |-> v],
                                   ![Dummy] = [Mem[Dummy] EXCEPT ![left] = n,
                                               ![right] = n]]
          ELSE
            [Mem EXCEPT ![n] = [left |-> oldLast, right |-> Dummy, value |-> v],
                                   ![oldLast] = [Mem[oldLast] EXCEPT ![right] = n],
                                   ![Dummy] = [Mem[Dummy] EXCEPT ![left] = n]]
    IN
      /\ freeList' = freeList \ {n}
      /\ Mem' = newMem
      /\ rVal' = [rVal EXCEPT ![p] = "none"]
      /\ valBag' = [valBag EXCEPT ![v] = valBag[v]+1]

(* Push left operation *)
PushLeft(p, v) ==
  \E n \in freeList :
    LET oldFirst == Mem[Dummy].right
        newMem ==
          IF oldFirst = Dummy THEN
            [Mem EXCEPT ![n] = [left |-> Dummy, right |-> Dummy, value |-> v],
                                   ![Dummy] = [Mem[Dummy] EXCEPT ![left] = n,
                                               ![right] = n]]
          ELSE
            [Mem EXCEPT ![n] = [left |-> Dummy, right |-> oldFirst, value |-> v],
                                   ![oldFirst] = [Mem[oldFirst] EXCEPT ![left] = n],
                                   ![Dummy] = [Mem[Dummy] EXCEPT ![right] = n]]
    IN
      /\ freeList' = freeList \ {n}
      /\ Mem' = newMem
      /\ rVal' = [rVal EXCEPT ![p] = "none"]
      /\ valBag' = [valBag EXCEPT ![v] = valBag[v]+1]

(* Pop right operation *)
PopRight(p) ==
  LET last == Mem[Dummy].left
  IN
    IF last = Dummy THEN
      /\ rVal' = [rVal EXCEPT ![p] = "empty"]
      /\ UNCHANGED <<Mem, freeList, valBag>>
    ELSE
      LET v   == Mem[last].value
          prev== Mem[last].left
          newMem ==
            [Mem EXCEPT ![prev] = [Mem[prev] EXCEPT ![right] = Dummy],
                                   ![Dummy] = [Mem[Dummy] EXCEPT ![left] = prev]]
      IN
        /\ valBag[v] > 0
        /\ rVal' = [rVal EXCEPT ![p] = v]
        /\ Mem' = newMem
        /\ freeList' = freeList \cup {last}
        /\ valBag' = [valBag EXCEPT ![v] = valBag[v]-1]

(* Pop left operation *)
PopLeft(p) ==
  LET first == Mem[Dummy].right
  IN
    IF first = Dummy THEN
      /\ rVal' = [rVal EXCEPT ![p] = "empty"]
      /\ UNCHANGED <<Mem, freeList, valBag>>
    ELSE
      LET v   == Mem[first].value
          next== Mem[first].right
          newMem ==
            [Mem EXCEPT ![next] = [Mem[next] EXCEPT ![left] = Dummy],
                                   ![Dummy] = [Mem[Dummy] EXCEPT ![right] = next]]
      IN
        /\ valBag[v] > 0
        /\ rVal' = [rVal EXCEPT ![p] = v]
        /\ Mem' = newMem
        /\ freeList' = freeList \cup {first}
        /\ valBag' = [valBag EXCEPT ![v] = valBag[v]-1]

(* Next action *)
PushRightAll ==
  \E p \in Procs : \E v \in Val : PushRight(p, v)

PushLeftAll ==
  \E p \in Procs : \E v \in Val : PushLeft(p, v)

PopAll ==
  \E p \in Procs : PopRight(p) \/ PopLeft(p)

Next == PushRightAll \/ PushLeftAll \/ PopAll

(* Invariants *)
InvValBag == \A v \in Val : valBag[v] >= 0
InvRVal   == \A p \in Procs : rVal[p] = "empty" \/ (rVal[p] \in Val)

Spec == Init /\ [][Next]_vars

===============================================================================