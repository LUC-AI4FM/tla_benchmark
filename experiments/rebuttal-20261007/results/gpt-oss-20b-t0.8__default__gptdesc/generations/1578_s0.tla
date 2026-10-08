---- MODULE DequeSpec ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Addr, Val, Nil, TestProcs

(*--------------------------------------------------------------------
  Shared state -------------------------------------------------------
--------------------------------------------------------------------*)

VARIABLE mem, leftHat, rightHat, freelist, valBag

Init ==
  /\ mem = [a \in Addr |-> <<val: {}, prev: Nil, next: Nil>>]
  /\ leftHat = Nil
  /\ rightHat = Nil
  /\ freelist = Addr
  /\ valBag = []

(*--------------------------------------------------------------------
  Helper definitions --------------------------------------------------
--------------------------------------------------------------------*)

DequeVals(addr) ==
  IF addr = Nil THEN [] 
  ELSE <<mem[addr].val>> \o DequeVals(mem[addr].next)

Invariant == valBag = DequeVals(leftHat)

Remove(seq, e) ==
  IF seq = [] THEN []
  ELSE IF First(seq) = e THEN Rest(seq)
      