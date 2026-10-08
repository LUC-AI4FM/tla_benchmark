------------------------------- MODULE SnarkDeque -------------------------------

CONSTANTS Procs, Val

VARIABLES Mem, freeList, LeftHat, RightHat, rVal, valBag

(*--algorithm snark_deque

variables 
  Mem = [a \in Address |-> <<Dummy, Dummy, defaultInitValue>>],
  freeList = {a \in Address : a # Dummy},
  LeftHat = Dummy,
  RightHat = Dummy,
  rVal = [p \in Procs |-> "empty"],
  valBag = {}

define
  DCAS(addr1, old1, new1, addr2, old2, new2) ==
    /\ Mem[addr1] = <<old1, _, _>>
    /\ Mem[addr2] = <<_, old2, _>>
    /\ Mem' = [Mem EXCEPT ![addr1] = <<new1, Mem[addr1][2], Mem[addr1][3]>>, ![addr2] = <<Mem[addr2][1], new2, Mem[addr2][3]>>]
end define;

pushRight ==
  \E addr \in freeList :
    /\ DCAS(RightHat, RightHat, addr, addr, Dummy, RightHat)
    /\ freeList' = freeList \ {addr}
    /\ Mem' = [Mem EXCEPT ![addr] = <<RightHat, Dummy, CHOOSE v \in Val : TRUE>>]
    /\ valBag' = (IF Cardinality(freeList) = 1 THEN valBag ELSE valBag \cup {CHOOSE v \in Val : TRUE})
    /\ RightHat' = addr

pushLeft ==
  \E addr \in freeList :
    /\ DCAS(LeftHat, Dummy, LeftHat, addr, LeftHat, Dummy)
    /\ freeList' = freeList \ {addr}
    /\ Mem' = [Mem EXCEPT ![addr] = <<Dummy, LeftHat, CHOOSE v \in Val : TRUE>>]
    /\ valBag' = (IF Cardinality(freeList) = 1 THEN valBag ELSE valBag \cup {CHOOSE v \in Val : TRUE})
    /\ LeftHat' = addr

popRight ==
  LET rightPtr == Mem[RightHat][2] IN
  CASE rightPtr # Dummy ->
    /\ DCAS(RightHat, RightHat, rightPtr, rightPtr, RightHat, Dummy)
    /\ freeList' = freeList \cup {rightPtr}
    /\ valBag' = valBag \ {Mem[rightPtr][3]}
    /\ rVal' = [rVal EXCEPT ![p] = Mem[rightPtr][3]]
  [] OTHER ->
    /\ rVal' = [rVal EXCEPT ![p] = "empty"]

popLeft ==
  LET leftPtr == Mem[LeftHat][1] IN
  CASE leftPtr # Dummy ->
    /\ DCAS(LeftHat, Dummy, LeftHat, leftPtr, LeftHat, Dummy)
    /\ freeList' = freeList \cup {leftPtr}
    /\ valBag' = valBag \ {Mem[leftPtr][3]}
    /\ rVal' = [rVal EXCEPT ![p] = Mem[leftPtr][3]]
  [] OTHER ->
    /\ rVal' = [rVal EXCEPT ![p] = "empty"]

process (p \in Procs)
begin
T1: while TRUE do
      either
        either pushRight
        or pushLeft
      then
        if Cardinality(freeList) = 0 then valBag' = valBag \ {CHOOSE v \in Val : TRUE}
      else
        either popRight
        or popLeft
      then
        assert rVal[p] = "empty" \/ rVal[p] \in valBag
    end if;
end while;
end process;

Init ==
  /\ Mem = [a \in Address |-> <<Dummy, Dummy, defaultInitValue>>]
  /\ freeList = {a \in Address : a # Dummy}
  /\ LeftHat = Dummy
  /\ RightHat = Dummy
  /\ rVal = [p \in Procs |-> "empty"]
  /\ valBag = {}

Next ==
  \/ \E p \in Procs : pushRight /\ UNCHANGED <<rVal[p], valBag>>
  \/ \E p \in Procs : pushLeft /\ UNCHANGED <<rVal[p], valBag>>
  \/ \E p \in Procs : popRight /\ UNCHANGED <<valBag - {rVal[p]}>>
  \/ \E p \in Procs : popLeft /\ UNCHANGED <<valBag - {rVal[p]}>>

Spec == Init /\ [][Next]_<<Mem, freeList, LeftHat, RightHat, rVal>>

LIVENESS ==
  \A p \in Procs : WF_next(T1)

==*)
=============================================================================