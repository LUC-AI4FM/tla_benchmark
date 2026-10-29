------------------------------- MODULE Snark -------------------------------
(***************************************************************************)
(* The "Snark" lock-free concurrent deque of Detlefs et al., implemented   *)
(* over a linked list in shared memory using a DCAS (Double                *)
(* Compare-and-Swap) primitive.                                            *)
(*                                                                         *)
(* Each test process loops forever. On each iteration it nondeterminist-   *)
(* ically pushes a value onto either end of the deque or pops from either  *)
(* end. The variable valBag records the multiset of values that are        *)
(* logically in the deque. It is used to check that no value is popped     *)
(* unless it was previously pushed.                                        *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Val, Address, Dummy, Procs

ASSUME Dummy \in Address

null == CHOOSE x : x \notin (Val \cup Address)

Node == [L : Address, R : Address, V : Val \cup {null}]

RetVal == Val \cup {null, "empty", "full", "okay"}

VARIABLES Mem, freeList, LeftHat, RightHat, rVal, valBag,
          pc, stack,
          nd, rh, rhR, rhL, lh, lhR, lhL, arg, tv

vars == << Mem, freeList, LeftHat, RightHat, rVal, valBag, pc, stack,
           nd, rh, rhR, rhL, lh, lhR, lhL, arg, tv >>

TypeOK ==
  /\ Mem \in [Address -> Node]
  /\ freeList \subseteq Address \ {Dummy}
  /\ LeftHat \in Address
  /\ RightHat \in Address
  /\ rVal \in [Procs -> RetVal]
  /\ valBag \in [Val -> Nat]
  /\ nd \in [Procs -> Address]
  /\ rh \in [Procs -> Address]
  /\ rhR \in [Procs -> Address]
  /\ rhL \in [Procs -> Address]
  /\ lh \in [Procs -> Address]
  /\ lhR \in [Procs -> Address]
  /\ lhL \in [Procs -> Address]
  /\ arg \in [Procs -> Val \cup {null}]
  /\ tv \in [Procs -> Val \cup {null}]

Init ==
  /\ Mem = [a \in Address |-> [L |-> Dummy, R |-> Dummy, V |-> null]]
  /\ freeList = Address \ {Dummy}
  /\ LeftHat = Dummy
  /\ RightHat = Dummy
  /\ rVal = [p \in Procs |-> null]
  /\ valBag = [v \in Val |-> 0]
  /\ pc = [p \in Procs |-> "T1"]
  /\ stack = [p \in Procs |-> << >>]
  /\ nd = [p \in Procs |-> Dummy]
  /\ rh = [p \in Procs |-> Dummy]
  /\ rhR = [p \in Procs |-> Dummy]
  /\ rhL = [p \in Procs |-> Dummy]
  /\ lh = [p \in Procs |-> Dummy]
  /\ lhR = [p \in Procs |-> Dummy]
  /\ lhL = [p \in Procs |-> Dummy]
  /\ arg = [p \in Procs |-> null]
  /\ tv = [p \in Procs |-> null]

(* Return from a procedure *)
Return(self) ==
  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]

Goto(self, lbl) == pc' = [pc EXCEPT ![self] = lbl]

(***************************************************************************)
(* procedure pushRight(v)                                                  *)
(***************************************************************************)
prA(self) ==
  /\ pc[self] = "prA"
  /\ IF freeList = {}
       THEN /\ rVal' = [rVal EXCEPT ![self] = "full"]
            /\ Return(self)
            /\ UNCHANGED << Mem, freeList, nd >>
       ELSE /\ \E a \in freeList :
                 /\ nd' = [nd EXCEPT ![self] = a]
                 /\ freeList' = freeList \ {a}
                 /\ Mem' = [Mem EXCEPT ![a] = [L |-> Dummy, R |-> Dummy,
                                               V |-> arg[self]]]
            /\ Goto(self, "prB")
            /\ UNCHANGED << rVal, stack >>
  /\ UNCHANGED << LeftHat, RightHat, valBag, rh, rhR, rhL, lh, lhR, lhL,
                  arg, tv >>

prB(self) ==
  /\ pc[self] = "prB"
  /\ rh' = [rh EXCEPT ![self] = RightHat]
  /\ Goto(self, "prC")
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, stack,
                  nd, rhR, rhL, lh, lhR, lhL, arg, tv >>

prC(self) ==
  /\ pc[self] = "prC"
  /\ rhR' = [rhR EXCEPT ![self] = Mem[rh[self]].R]
  /\ Goto(self, "prD")
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, stack,
                  nd, rh, rhL, lh, lhR, lhL, arg, tv >>

prD(self) ==
  /\ pc[self] = "prD"
  /\ IF rhR[self] = rh[self]
       THEN /\ Mem' = [Mem EXCEPT ![nd[self]].L = Dummy]
            /\ Goto(self, "prE")
       ELSE /\ Mem' = [Mem EXCEPT ![nd[self]].L = rh[self]]
            /\ Goto(self, "prF")
  /\ UNCHANGED << freeList, LeftHat, RightHat, rVal, valBag, stack,
                  nd, rh, rhR, rhL, lh, lhR, lhL, arg, tv >>

prE(self) ==
  /\ pc[self] = "prE"
  /\ lh' = [lh EXCEPT ![self] = LeftHat]
  /\ Goto(self, "prG")
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, stack,
                  nd, rh, rhR, rhL, lhR, lhL, arg, tv >>

(* DCAS(&RightHat, &LeftHat, rh, lh, nd, nd) *)
prG(self) ==
  /\ pc[self] = "prG"
  /\ IF RightHat = rh[self] /\ LeftHat = lh[self]
       THEN /\ RightHat' = nd[self]
            /\ LeftHat' = nd[self]
            /\ rVal' = [rVal EXCEPT ![self] = "okay"]
            /\ Return(self)
       ELSE /\ Goto(self, "prB")
            /\ UNCHANGED << RightHat, LeftHat, rVal, stack >>
  /\ UNCHANGED << Mem, freeList, valBag, nd, rh, rhR, rhL, lh, lhR, lhL,
                  arg, tv >>

(* DCAS(&RightHat, &rh->R, rh, rhR, nd, nd) *)
prF(self) ==
  /\ pc[self] = "prF"
  /\ IF RightHat = rh[self] /\ Mem[rh[self]].R = rhR[self]
       THEN /\ RightHat' = nd[self]
            /\ Mem' = [Mem EXCEPT ![rh[self]].R = nd[self]]
            /\ rVal' = [rVal EXCEPT ![self] = "okay"]
            /\ Return(self)
       ELSE /\ Goto(self, "prB")
            /\ UNCHANGED << RightHat, Mem, rVal, stack >>
  /\ UNCHANGED << freeList, LeftHat, valBag, nd, rh, rhR, rhL, lh, lhR,
                  lhL, arg, tv >>

pushRight(self) == prA(self) \/ prB(self) \/ prC(self) \/ prD(self)
                     \/ prE(self) \/ prG(self) \/ prF(self)

(***************************************************************************)
(* procedure pushLeft(v)                                                   *)
(***************************************************************************)
plA(self) ==
  /\ pc[self] = "plA"
  /\ IF freeList = {}
       THEN /\ rVal' = [rVal EXCEPT ![self] = "full"]
            /\ Return(self)
            /\ UNCHANGED << Mem, freeList, nd >>
       ELSE /\ \E a \in freeList :
                 /\ nd' = [nd EXCEPT ![self] = a]
                 /\ freeList' = freeList \ {a}
                 /\ Mem' = [Mem EXCEPT ![a] = [L |-> Dummy, R |-> Dummy,
                                               V |-> arg[self]]]
            /\ Goto(self, "plB")
            /\ UNCHANGED << rVal, stack >>
  /\ UNCHANGED << LeftHat, RightHat, valBag, rh, rhR, rhL, lh, lhR, lhL,
                  arg, tv >>

plB(self) ==
  /\ pc[self] = "plB"
  /\ lh' = [lh EXCEPT ![self] = LeftHat]
  /\ Goto(self, "plC")
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, stack,
                  nd, rh, rhR, rhL, lhR, lhL, arg, tv >>

plC(self) ==
  /\ pc[self] = "plC"
  /\ lhL' = [lhL EXCEPT ![self] = Mem[lh[self]].L]
  /\ Goto(self, "plD")
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, stack,
                  nd, rh, rhR, rhL, lh, lhR, arg, tv >>

plD(self) ==
  /\ pc[self] = "plD"
  /\ IF lhL[self] = lh[self]
       THEN /\ Mem' = [Mem EXCEPT ![nd[self]].R = Dummy]
            /\ Goto(self, "plE")
       ELSE /\ Mem' = [Mem EXCEPT ![nd[self]].R = lh[self]]
            /\ Goto(self, "plF")
  /\ UNCHANGED << freeList, LeftHat, RightHat, rVal, valBag, stack,
                  nd, rh, rhR, rhL, lh, lhR, lhL, arg, tv >>

plE(self) ==
  /\ pc[self] = "plE"
  /\ rh' = [rh EXCEPT ![self] = RightHat]
  /\ Goto(self, "plG")
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, stack,
                  nd, rhR, rhL, lh, lhR, lhL, arg, tv >>

(* DCAS(&LeftHat, &RightHat, lh, rh, nd, nd) *)
plG(self) ==
  /\ pc[self] = "plG"
  /\ IF LeftHat = lh[self] /\ RightHat = rh[self]
       THEN /\ LeftHat' = nd[self]
            /\ RightHat' = nd[self]
            /\ rVal' = [rVal EXCEPT ![self] = "okay"]
            /\ Return(self)
       ELSE /\ Goto(self, "plB")
            /\ UNCHANGED << RightHat, LeftHat, rVal, stack >>
  /\ UNCHANGED << Mem, freeList, valBag, nd, rh, rhR, rhL, lh, lhR, lhL,
                  arg, tv >>

(* DCAS(&LeftHat, &lh->L, lh, lhL, nd, nd) *)
plF(self) ==
  /\ pc[self] = "plF"
  /\ IF LeftHat = lh[self] /\ Mem[lh[self]].L = lhL[self]
       THEN /\ LeftHat' = nd[self]
            /\ Mem' = [Mem EXCEPT ![lh[self]].L = nd[self]]
            /\ rVal' = [rVal EXCEPT ![self] = "okay"]
            /\ Return(self)
       ELSE /\ Goto(self, "plB")
            /\ UNCHANGED << LeftHat, Mem, rVal, stack >>
  /\ UNCHANGED << freeList, RightHat, valBag, nd, rh, rhR, rhL, lh, lhR,
                  lhL, arg, tv >>

pushLeft(self) == plA(self) \/ plB(self) \/ plC(self) \/ plD(self)
                    \/ plE(self) \/ plG(self) \/ plF(self)

(***************************************************************************)
(* procedure popRight()                                                    *)
(***************************************************************************)
rpA(self) ==
  /\ pc[self] = "rpA"
  /\ rh' = [rh EXCEPT ![self] = RightHat]
  /\ Goto(self, "rpB")
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, stack,
                  nd, rhR, rhL, lh, lhR, lhL, arg, tv >>

rpB(self) ==
  /\ pc[self] = "rpB"
  /\ lh' = [lh EXCEPT ![self] = LeftHat]
  /\ Goto(self, "rpC")
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, stack,
                  nd, rh, rhR, rhL, lhR, lhL, arg, tv >>

rpC(self) ==
  /\ pc[self] = "rpC"
  /\ IF Mem[rh[self]].R = rh[self]
       THEN /\ rVal' = [rVal EXCEPT ![self] = "empty"]
            /\ Return(self)
       ELSE /\ IF rh[self] = lh[self]
                 THEN Goto(self, "rpD")
                 ELSE Goto(self, "rpE")
            /\ UNCHANGED << rVal, stack >>
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, valBag, nd, rh, rhR,
                  rhL, lh, lhR, lhL, arg, tv >>

(* DCAS(&RightHat, &LeftHat, rh, lh, Dummy, Dummy) *)
rpD(self) ==
  /\ pc[self] = "rpD"
  /\ IF RightHat = rh[self] /\ LeftHat = lh[self]
       THEN /\ RightHat' = Dummy
            /\ LeftHat' = Dummy
            /\ Goto(self, "rpF")
       ELSE /\ Goto(self, "rpA")
            /\ UNCHANGED << RightHat, LeftHat >>
  /\ UNCHANGED << Mem, freeList, rVal, valBag, stack, nd, rh, rhR, rhL,
                  lh, lhR, lhL, arg, tv >>

rpE(self) ==
  /\ pc[self] = "rpE"
  /\ rhL' = [rhL EXCEPT ![self] = Mem[rh[self]].L]
  /\ Goto(self, "rpG")
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, stack,
                  nd, rh, rhR, lh, lhR, lhL, arg, tv >>

(* DCAS(&RightHat, &rh->L, rh, rhL, rhL, rh) *)
rpG(self) ==
  /\ pc[self] = "rpG"
  /\ IF RightHat = rh[self] /\ Mem[rh[self]].L = rhL[self]
       THEN /\ RightHat' = rhL[self]
            /\ Mem' = [Mem EXCEPT ![rh[self]].L = rh[self]]
            /\ Goto(self, "rpF")
       ELSE /\ Goto(self, "rpA")
            /\ UNCHANGED << RightHat, Mem >>
  /\ UNCHANGED << freeList, LeftHat, rVal, valBag, stack, nd, rh, rhR,
                  rhL, lh, lhR, lhL, arg, tv >>

rpF(self) ==
  /\ pc[self] = "rpF"
  /\ rVal' = [rVal EXCEPT ![self] = Mem[rh[self]].V]
  /\ Return(self)
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, valBag, nd, rh, rhR,
                  rhL, lh, lhR, lhL, arg, tv >>

popRight(self) == rpA(self) \/ rpB(self) \/ rpC(self) \/ rpD(self)
                    \/ rpE(self) \/ rpG(self) \/ rpF(self)

(***************************************************************************)
(* procedure popLeft()                                                     *)
(***************************************************************************)
lpA(self) ==
  /\ pc[self] = "lpA"
  /\ lh' = [lh EXCEPT ![self] = LeftHat]
  /\ Goto(self, "lpB")
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, stack,
                  nd, rh, rhR, rhL, lhR, lhL, arg, tv >>

lpB(self) ==
  /\ pc[self] = "lpB"
  /\ rh' = [rh EXCEPT ![self] = RightHat]
  /\ Goto(self, "lpC")
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, stack,
                  nd, rhR, rhL, lh, lhR, lhL, arg, tv >>

lpC(self) ==
  /\ pc[self] = "lpC"
  /\ IF Mem[lh[self]].L = lh[self]
       THEN /\ rVal' = [rVal EXCEPT ![self] = "empty"]
            /\ Return(self)
       ELSE /\ IF lh[self] = rh[self]
                 THEN Goto(self, "lpD")
                 ELSE Goto(self, "lpE")
            /\ UNCHANGED << rVal, stack >>
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, valBag, nd, rh, rhR,
                  rhL, lh, lhR, lhL, arg, tv >>

(* DCAS(&LeftHat, &RightHat, lh, rh, Dummy, Dummy) *)
lpD(self) ==
  /\ pc[self] = "lpD"
  /\ IF LeftHat = lh[self] /\ RightHat = rh[self]
       THEN /\ LeftHat' = Dummy
            /\ RightHat' = Dummy
            /\ Goto(self, "lpF")
       ELSE /\ Goto(self, "lpA")
            /\ UNCHANGED << RightHat, LeftHat >>
  /\ UNCHANGED << Mem, freeList, rVal, valBag, stack, nd, rh, rhR, rhL,
                  lh, lhR, lhL, arg, tv >>

lpE(self) ==
  /\ pc[self] = "lpE"
  /\ lhR' = [lhR EXCEPT ![self] = Mem[lh[self]].R]
  /\ Goto(self, "lpG")
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, valBag, stack,
                  nd, rh, rhR, rhL, lh, lhL, arg, tv >>

(* DCAS(&LeftHat, &lh->R, lh, lhR, lhR, lh) *)
lpG(self) ==
  /\ pc[self] = "lpG"
  /\ IF LeftHat = lh[self] /\ Mem[lh[self]].R = lhR[self]
       THEN /\ LeftHat' = lhR[self]
            /\ Mem' = [Mem EXCEPT ![lh[self]].R = lh[self]]
            /\ Goto(self, "lpF")
       ELSE /\ Goto(self, "lpA")
            /\ UNCHANGED << LeftHat, Mem >>
  /\ UNCHANGED << freeList, RightHat, rVal, valBag, stack, nd, rh, rhR,
                  rhL, lh, lhR, lhL, arg, tv >>

lpF(self) ==
  /\ pc[self] = "lpF"
  /\ rVal' = [rVal EXCEPT ![self] = Mem[lh[self]].V]
  /\ Return(self)
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, valBag, nd, rh, rhR,
                  rhL, lh, lhR, lhL, arg, tv >>

popLeft(self) == lpA(self) \/ lpB(self) \/ lpC(self) \/ lpD(self)
                   \/ lpE(self) \/ lpG(self) \/ lpF(self)

(***************************************************************************)
(* Test processes                                                          *)
(***************************************************************************)
Call(self, proc, entry, ret) ==
  /\ stack' = [stack EXCEPT ![self] =
                 << [procedure |-> proc, pc |-> ret] >> \o stack[self]]
  /\ pc' = [pc EXCEPT ![self] = entry]

T1(self) ==
  /\ pc[self] = "T1"
  /\ \/ \E v \in Val :
           /\ valBag' = [valBag EXCEPT ![v] = @ + 1]
           /\ tv' = [tv EXCEPT ![self] = v]
           /\ arg' = [arg EXCEPT ![self] = v]
           /\ Call(self, "pushRight", "prA", "T2")
     \/ \E v \in Val :
           /\ valBag' = [valBag EXCEPT ![v] = @ + 1]
           /\ tv' = [tv EXCEPT ![self] = v]
           /\ arg' = [arg EXCEPT ![self] = v]
           /\ Call(self, "pushLeft", "plA", "T2")
     \/ /\ Call(self, "popRight", "rpA", "T3")
        /\ UNCHANGED << valBag, tv, arg >>
     \/ /\ Call(self, "popLeft", "lpA", "T3")
        /\ UNCHANGED << valBag, tv, arg >>
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, nd, rh, rhR,
                  rhL, lh, lhR, lhL >>

(* After a push: roll back valBag if the queue was full *)
T2(self) ==
  /\ pc[self] = "T2"
  /\ valBag' = IF rVal[self] = "full"
                 THEN [valBag EXCEPT ![tv[self]] = @ - 1]
                 ELSE valBag
  /\ Goto(self, "T1")
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, stack, nd, rh,
                  rhR, rhL, lh, lhR, lhL, arg, tv >>

(* After a pop: check that the popped value was in valBag *)
T3(self) ==
  /\ pc[self] = "T3"
  /\ IF rVal[self] = "empty"
       THEN valBag' = valBag
       ELSE /\ Assert(rVal[self] \in Val /\ valBag[rVal[self]] > 0,
                      "Popped a value that was not pushed")
            /\ valBag' = [valBag EXCEPT ![rVal[self]] = @ - 1]
  /\ Goto(self, "T1")
  /\ UNCHANGED << Mem, freeList, LeftHat, RightHat, rVal, stack, nd, rh,
                  rhR, rhL, lh, lhR, lhL, arg, tv >>

test(self) == T1(self) \/ T2(self) \/ T3(self)

Next == \E self \in Procs :
          \/ test(self)
          \/ pushRight(self) \/ pushLeft(self)
          \/ popRight(self) \/ popLeft(self)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
ValBagOK == \A v \in Val : valBag[v] >= 0

Liveness == \A p \in Procs : []<>(pc[p] = "T1")

Symmetry == Permutations(Address \ {Dummy}) \cup Permutations(Procs)

=============================================================================