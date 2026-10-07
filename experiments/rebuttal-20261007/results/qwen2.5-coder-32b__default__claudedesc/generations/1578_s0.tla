------------------------------- MODULE SnarkDeque -------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Procs, Val, Address, Dummy

VARIABLES Mem, freeList, LeftHat, RightHat, rVal, valBag

DCAS(mem, addr1, oldVal1, newVal1, addr2, oldVal2, newVal2) ==
  /\ mem[addr1] = oldVal1
  /\ mem[addr2] = oldVal2
  /\ mem' = [mem EXCEPT ![addr1] = newVal1, ![addr2] = newVal2]

Init ==
  /\ freeList \subseteq Address
  /\ LeftHat = Dummy
  /\ RightHat = Dummy
  /\ Mem = [a \in Address |-> <<Dummy, Dummy, "">>]
  /\ Mem[Dummy] = <<Dummy, Dummy, "">>
  /\ rVal = [p \in Procs |-> ""]
  /\ valBag = {}

PushRight(p) ==
  LET newValue == CHOOSE v \in Val: TRUE
      newNode == CHOOSE a \in freeList: TRUE
  IN
    /\ newNode \in freeList
    /\ Mem[newNode] = <<Dummy, Dummy, newValue>>
    /\ \/ DCAS(Mem, RightHat, <<lh, rh, rv>>, <<lh, newNode, rv>>, newNode, rh, lh)
       \/ PushRight(p)

PushLeft(p) ==
  LET newValue == CHOOSE v \in Val: TRUE
      newNode == CHOOSE a \in freeList: TRUE
  IN
    /\ newNode \in freeList
    /\ Mem[newNode] = <<Dummy, Dummy, newValue>>
    /\ \/ DCAS(Mem, LeftHat, <<lh, rh, rv>>, <<newNode, lh, rv>>, newNode, rh, lh)
       \/ PushLeft(p)

PopRight(p) ==
  LET oldTail == CHOOSE a \in Address: TRUE
      newTail == Mem[oldTail][1]
  IN
    /\ oldTail = RightHat
    /\ newTail # Dummy
    /\ DCAS(Mem, RightHat, <<lh, oldTail, rv>>, <<lh, newTail, rv>>, oldTail, lh, newTail)
    /\ rVal' = [rVal EXCEPT ![p] = Mem[oldTail][3]]
    /\ freeList' = freeList \cup {oldTail}

PopLeft(p) ==
  LET oldHead == CHOOSE a \in Address: TRUE
      newHead == Mem[oldHead][2]
  IN
    /\ oldHead = LeftHat
    /\ newHead # Dummy
    /\ DCAS(Mem, LeftHat, <<oldHead, rh, rv>>, <<newHead, rh, rv>>, oldHead, rh, newHead)
    /\ rVal' = [rVal EXCEPT ![p] = Mem[oldHead][3]]
    /\ freeList' = freeList \cup {oldHead}

T1(p) ==
  \/ PushRight(p)
  \/ PushLeft(p)
  \/ PopRight(p)
  \/ PopLeft(p)

Next ==
  \E p \in Procs: T1(p)

Spec ==
  Init /\ [][Next]_<<Mem, freeList, LeftHat, RightHat, rVal>>

Liveness ==
  \A p \in Procs: WF_next(T1(p))

THEOREM Spec => []<>(\E p \in Procs: T1(p))

=============================================================================