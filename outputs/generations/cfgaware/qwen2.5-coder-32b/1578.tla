------------------------------- MODULE DoubleEndedQueue ------------------------------

CONSTANTS Val

VARIABLES mem, leftHat, rightHat, freeList, pc, valBag

(*--algorithm double_ended_queue
variables 
  mem = [a \in 1..2000000 -> <<NIL, NIL>>, NIL>>,  (* Memory mapping from addresses to node records *)
  leftHat = 0,                                      (* Left hat pointer *)
  rightHat = 0,                                     (* Right hat pointer *)
  freeList = 1..2000000,                            (* Free list for allocation *)
  pc = [p \in Procs -> "T1"],                       (* Program counters for each process *)
  valBag = {}                                       (* Multiset-like consistency check *)

process (p \in Procs)
begin
T1: either
      await /\ freeList /= {}
           /\ leftHat # rightHat
      pushLeft:
        with addr \in freeList do
          mem[addr] := <<NIL, leftHat, val>>;
          freeList := freeList \ {addr};
          mem[leftHat][2] := addr;
          leftHat := addr;
          valBag := valBag \cup {val}
    or
      await /\ freeList /= {}
           /\ leftHat # rightHat
      pushRight:
        with addr \in freeList do
          mem[addr] := <<rightHat, NIL, val>>;
          freeList := freeList \ {addr};
          mem[rightHat][1] := addr;
          rightHat := addr;
          valBag := valBag \cup {val}
    or
      await leftHat # rightHat
      popLeft:
        with addr \in SUBSET 1..2000000 do
          if mem[leftHat][1] = addr then
            let nextAddr == mem[addr][2] in
              mem[leftHat][1] := NIL;
              leftHat := nextAddr;
              freeList := freeList \cup {addr};
              valBag := valBag \ {mem[addr][3]}
          end if
    or
      await leftHat # rightHat
      popRight:
        with addr \in SUBSET 1..2000000 do
          if mem[rightHat][2] = addr then
            let prevAddr == mem[addr][1] in
              mem[rightHat][2] := NIL;
              rightHat := prevAddr;
              freeList := freeList \cup {addr};
              valBag := valBag \ {mem[addr][3]}
          end if
    or
      skip
  end either;
  goto T1
end process

end algorithm *)

Spec == /\ Init
        /\ \A p \in Procs : SpecProc(p)

Init == /\ mem = [a \in 1..2000000 -> <<NIL, NIL>>, NIL>>]
        /\ leftHat = 0
        /\ rightHat = 0
        /\ freeList = 1..2000000
        /\ pc = [p \in Procs -> "T1"]
        /\ valBag = {}

SpecProc(p) == 
  /\ \A i \in Nat : <<pc[p][i], mem[i], leftHat[i], rightHat[i], freeList[i], valBag[i]>> \in Behavior(p)

Behavior(p) == INSTANCE BehaviorOfProcess <<p>>

INSTANCE Spec

defaultInitValue == <<0, [a \in 1..2000000 -> <<NIL, NIL>>, NIL>>, 0, 0, 1..2000000, {}>>

=============================================================================