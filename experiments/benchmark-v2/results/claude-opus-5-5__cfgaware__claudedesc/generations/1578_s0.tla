------------------------------- MODULE Snark -------------------------------
EXTENDS Naturals, TLC, FiniteSets

CONSTANTS Val, Address, Dummy, Procs, null, GC, defaultInitValue

ASSUME Dummy \in Address
ASSUME null \notin Val

VARIABLES Mem, freeList, LeftHat, RightHat, rVal, valBag,
          pc, nd, rh, lh, tmp, pushVal

vars == <<Mem, freeList, LeftHat, RightHat, rVal, valBag,
          pc, nd, rh, lh, tmp, pushVal>>

-----------------------------------------------------------------------------
Init ==
  /\ Mem = [a \in Address |-> [L |-> Dummy, R |-> Dummy, V |-> null]]
  /\ freeList = Address \ {Dummy}
  /\ LeftHat = Dummy
  /\ RightHat = Dummy
  /\ rVal = [p \in Procs |-> defaultInitValue]
  /\ valBag = [v \in Val |-> 0]
  /\ pc = [p \in Procs |-> "T1"]
  /\ nd = [p \in Procs |-> defaultInitValue]
  /\ rh = [p \in Procs |-> defaultInitValue]
  /\ lh = [p \in Procs |-> defaultInitValue]
  /\ tmp = [p \in Procs |-> defaultInitValue]
  /\ pushVal = [p \in Procs |-> defaultInitValue]

Goto(p, lbl) == pc' = [pc EXCEPT ![p] = lbl]

-----------------------------------------------------------------------------
(* Test process main loop *)
T1(p) ==
  /\ pc[p] = "T1"
  /\ \/ /\ \E v \in Val :
             /\ pushVal' = [pushVal EXCEPT ![p] = v]
             /\ valBag' = [valBag EXCEPT ![v] = @ + 1]
             /\ \/ Goto(p, "PR1")
                \/ Goto(p, "PL1")
        /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, nd, rh, lh, tmp>>
     \/ /\ \/ Goto(p, "PoR1")
           \/ Goto(p, "PoL1")
        /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag,
                       nd, rh, lh, tmp, pushVal>>

T2push(p) ==
  /\ pc[p] = "T2push"
  /\ IF rVal[p] = "full"
       THEN valBag' = [valBag EXCEPT ![pushVal[p]] = @ - 1]
       ELSE UNCHANGED valBag
  /\ Goto(p, "T1")
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, nd, rh, lh, tmp, pushVal>>

T2pop(p) ==
  /\ pc[p] = "T2pop"
  /\ IF rVal[p] /= "empty"
       THEN /\ Assert(rVal[p] \in Val /\ valBag[rVal[p]] > 0,
                      "Popped a value that was not pushed")
            /\ valBag' = [valBag EXCEPT ![rVal[p]] = @ - 1]
       ELSE UNCHANGED valBag
  /\ Goto(p, "T1")
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, nd, rh, lh, tmp, pushVal>>

-----------------------------------------------------------------------------
(* pushRight *)
PR1(p) ==
  /\ pc[p] = "PR1"
  /\ IF freeList = {}
       THEN /\ rVal' = [rVal EXCEPT ![p] = "full"]
            /\ Goto(p, "T2push")
            /\ UNCHANGED <<Mem, freeList, nd>>
       ELSE \E a \in freeList :
              /\ nd' = [nd EXCEPT ![p] = a]
              /\ freeList' = freeList \ {a}
              /\ Mem' = [Mem EXCEPT ![a].R = Dummy, ![a].V = pushVal[p]]
              /\ Goto(p, "PR2")
              /\ UNCHANGED rVal
  /\ UNCHANGED <<LeftHat, RightHat, valBag, rh, lh, tmp, pushVal>>

PR2(p) ==
  /\ pc[p] = "PR2"
  /\ rh' = [rh EXCEPT ![p] = RightHat]
  /\ Goto(p, "PR3")
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, nd, lh, tmp, pushVal>>

PR3(p) ==
  /\ pc[p] = "PR3"
  /\ tmp' = [tmp EXCEPT ![p] = Mem[rh[p]].R]
  /\ Goto(p, "PR4")
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, nd, rh, lh, pushVal>>

PR4(p) ==
  /\ pc[p] = "PR4"
  /\ IF tmp[p] = rh[p]
       THEN /\ Mem' = [Mem EXCEPT ![nd[p]].L = Dummy]
            /\ Goto(p, "PR5")
       ELSE /\ Mem' = [Mem EXCEPT ![nd[p]].L = rh[p]]
            /\ Goto(p, "PR7")
  /\ UNCHANGED <<freeList, LeftHat, RightHat, rVal, valBag, nd, rh, lh, tmp, pushVal>>

PR5(p) ==
  /\ pc[p] = "PR5"
  /\ lh' = [lh EXCEPT ![p] = LeftHat]
  /\ Goto(p, "PR6")
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, nd, rh, tmp, pushVal>>

PR6(p) ==  \* DCAS(&RightHat, &LeftHat, rh, lh, nd, nd)
  /\ pc[p] = "PR6"
  /\ IF RightHat = rh[p] /\ LeftHat = lh[p]
       THEN /\ RightHat' = nd[p]
            /\ LeftHat' = nd[p]
            /\ rVal' = [rVal EXCEPT ![p] = "okay"]
            /\ Goto(p, "T2push")
       ELSE /\ Goto(p, "PR2")
            /\ UNCHANGED <<RightHat, LeftHat, rVal>>
  /\ UNCHANGED <<Mem, freeList, valBag, nd, rh, lh, tmp, pushVal>>

PR7(p) ==  \* DCAS(&RightHat, &rh->R, rh, rhR, nd, nd)
  /\ pc[p] = "PR7"
  /\ IF RightHat = rh[p] /\ Mem[rh[p]].R = tmp[p]
       THEN /\ RightHat' = nd[p]
            /\ Mem' = [Mem EXCEPT ![rh[p]].R = nd[p]]
            /\ rVal' = [rVal EXCEPT ![p] = "okay"]
            /\ Goto(p, "T2push")
       ELSE /\ Goto(p, "PR2")
            /\ UNCHANGED <<RightHat, Mem, rVal>>
  /\ UNCHANGED <<freeList, LeftHat, valBag, nd, rh, lh, tmp, pushVal>>

-----------------------------------------------------------------------------
(* pushLeft *)
PL1(p) ==
  /\ pc[p] = "PL1"
  /\ IF freeList = {}
       THEN /\ rVal' = [rVal EXCEPT ![p] = "full"]
            /\ Goto(p, "T2push")
            /\ UNCHANGED <<Mem, freeList, nd>>
       ELSE \E a \in freeList :
              /\ nd' = [nd EXCEPT ![p] = a]
              /\ freeList' = freeList \ {a}
              /\ Mem' = [Mem EXCEPT ![a].L = Dummy, ![a].V = pushVal[p]]
              /\ Goto(p, "PL2")
              /\ UNCHANGED rVal
  /\ UNCHANGED <<LeftHat, RightHat, valBag, rh, lh, tmp, pushVal>>

PL2(p) ==
  /\ pc[p] = "PL2"
  /\ lh' = [lh EXCEPT ![p] = LeftHat]
  /\ Goto(p, "PL3")
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, nd, rh, tmp, pushVal>>

PL3(p) ==
  /\ pc[p] = "PL3"
  /\ tmp' = [tmp EXCEPT ![p] = Mem[lh[p]].L]
  /\ Goto(p, "PL4")
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, nd, rh, lh, pushVal>>

PL4(p) ==
  /\ pc[p] = "PL4"
  /\ IF tmp[p] = lh[p]
       THEN /\ Mem' = [Mem EXCEPT ![nd[p]].R = Dummy]
            /\ Goto(p, "PL5")
       ELSE /\ Mem' = [Mem EXCEPT ![nd[p]].R = lh[p]]
            /\ Goto(p, "PL7")
  /\ UNCHANGED <<freeList, LeftHat, RightHat, rVal, valBag, nd, rh, lh, tmp, pushVal>>

PL5(p) ==
  /\ pc[p] = "PL5"
  /\ rh' = [rh EXCEPT ![p] = RightHat]
  /\ Goto(p, "PL6")
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, nd, lh, tmp, pushVal>>

PL6(p) ==  \* DCAS(&LeftHat, &RightHat, lh, rh, nd, nd)
  /\ pc[p] = "PL6"
  /\ IF LeftHat = lh[p] /\ RightHat = rh[p]
       THEN /\ LeftHat' = nd[p]
            /\ RightHat' = nd[p]
            /\ rVal' = [rVal EXCEPT ![p] = "okay"]
            /\ Goto(p, "T2push")
       ELSE /\ Goto(p, "PL2")
            /\ UNCHANGED <<RightHat, LeftHat, rVal>>
  /\ UNCHANGED <<Mem, freeList, valBag, nd, rh, lh, tmp, pushVal>>

PL7(p) ==  \* DCAS(&LeftHat, &lh->L, lh, lhL, nd, nd)
  /\ pc[p] = "PL7"
  /\ IF LeftHat = lh[p] /\ Mem[lh[p]].L = tmp[p]
       THEN /\ LeftHat' = nd[p]
            /\ Mem' = [Mem EXCEPT ![lh[p]].L = nd[p]]
            /\ rVal' = [rVal EXCEPT ![p] = "okay"]
            /\ Goto(p, "T2push")
       ELSE /\ Goto(p, "PL2")
            /\ UNCHANGED <<LeftHat, Mem, rVal>>
  /\ UNCHANGED <<freeList, RightHat, valBag, nd, rh, lh, tmp, pushVal>>

-----------------------------------------------------------------------------
(* popRight *)
PoR1(p) ==
  /\ pc[p] = "PoR1"
  /\ rh' = [rh EXCEPT ![p] = RightHat]
  /\ Goto(p, "PoR2")
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, nd, lh, tmp, pushVal>>

PoR2(p) ==
  /\ pc[p] = "PoR2"
  /\ lh' = [lh EXCEPT ![p] = LeftHat]
  /\ Goto(p, "PoR3")
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, nd, rh, tmp, pushVal>>

PoR3(p) ==
  /\ pc[p] = "PoR3"
  /\ IF Mem[rh[p]].R = rh[p]
       THEN /\ rVal' = [rVal EXCEPT ![p] = "empty"]
            /\ Goto(p, "T2pop")
       ELSE /\ IF rh[p] = lh[p] THEN Goto(p, "PoR4") ELSE Goto(p, "PoR5")
            /\ UNCHANGED rVal
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, valBag, nd, rh, lh, tmp, pushVal>>

PoR4(p) ==  \* DCAS(&RightHat, &LeftHat, rh, lh, Dummy, Dummy)
  /\ pc[p] = "PoR4"
  /\ IF RightHat = rh[p] /\ LeftHat = lh[p]
       THEN /\ RightHat' = Dummy
            /\ LeftHat' = Dummy
            /\ Goto(p, "PoR6")
       ELSE /\ Goto(p, "PoR1")
            /\ UNCHANGED <<RightHat, LeftHat>>
  /\ UNCHANGED <<Mem, freeList, rVal, valBag, nd, rh, lh, tmp, pushVal>>

PoR6(p) ==
  /\ pc[p] = "PoR6"
  /\ rVal' = [rVal EXCEPT ![p] = Mem[rh[p]].V]
  /\ Goto(p, "PoRFree")
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, valBag, nd, rh, lh, tmp, pushVal>>

PoR5(p) ==
  /\ pc[p] = "PoR5"
  /\ tmp' = [tmp EXCEPT ![p] = Mem[rh[p]].L]
  /\ Goto(p, "PoR7")
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, nd, rh, lh, pushVal>>

PoR7(p) ==  \* DCAS(&RightHat, &rh->L, rh, rhL, rhL, rh)
  /\ pc[p] = "PoR7"
  /\ IF RightHat = rh[p] /\ Mem[rh[p]].L = tmp[p]
       THEN /\ RightHat' = tmp[p]
            /\ Mem' = [Mem EXCEPT ![rh[p]].L = rh[p]]
            /\ Goto(p, "PoR8")
       ELSE /\ Goto(p, "PoR1")
            /\ UNCHANGED <<RightHat, Mem>>
  /\ UNCHANGED <<freeList, LeftHat, rVal, valBag, nd, rh, lh, tmp, pushVal>>

PoR8(p) ==
  /\ pc[p] = "PoR8"
  /\ rVal' = [rVal EXCEPT ![p] = Mem[rh[p]].V]
  /\ Goto(p, "PoR9")
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, valBag, nd, rh, lh, tmp, pushVal>>

PoR9(p) ==
  /\ pc[p] = "PoR9"
  /\ Mem' = [Mem EXCEPT ![rh[p]].R = Dummy]
  /\ Goto(p, "PoRFree")
  /\ UNCHANGED <<freeList, LeftHat, RightHat, rVal, valBag, nd, rh, lh, tmp, pushVal>>

PoRFree(p) ==
  /\ pc[p] = "PoRFree"
  /\ IF GC THEN freeList' = freeList \cup {rh[p]}
           ELSE UNCHANGED freeList
  /\ Goto(p, "T2pop")
  /\ UNCHANGED <<Mem, LeftHat, RightHat, rVal, valBag, nd, rh, lh, tmp, pushVal>>

-----------------------------------------------------------------------------
(* popLeft *)
PoL1(p) ==
  /\ pc[p] = "PoL1"
  /\ lh' = [lh EXCEPT ![p] = LeftHat]
  /\ Goto(p, "PoL2")
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, nd, rh, tmp, pushVal>>

PoL2(p) ==
  /\ pc[p] = "PoL2"
  /\ rh' = [rh EXCEPT ![p] = RightHat]
  /\ Goto(p, "PoL3")
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, nd, lh, tmp, pushVal>>

PoL3(p) ==
  /\ pc[p] = "PoL3"
  /\ IF Mem[lh[p]].L = lh[p]
       THEN /\ rVal' = [rVal EXCEPT ![p] = "empty"]
            /\ Goto(p, "T2pop")
       ELSE /\ IF lh[p] = rh[p] THEN Goto(p, "PoL4") ELSE Goto(p, "PoL5")
            /\ UNCHANGED rVal
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, valBag, nd, rh, lh, tmp, pushVal>>

PoL4(p) ==  \* DCAS(&LeftHat, &RightHat, lh, rh, Dummy, Dummy)
  /\ pc[p] = "PoL4"
  /\ IF LeftHat = lh[p] /\ RightHat = rh[p]
       THEN /\ LeftHat' = Dummy
            /\ RightHat' = Dummy
            /\ Goto(p, "PoL6")
       ELSE /\ Goto(p, "PoL1")
            /\ UNCHANGED <<RightHat, LeftHat>>
  /\ UNCHANGED <<Mem, freeList, rVal, valBag, nd, rh, lh, tmp, pushVal>>

PoL6(p) ==
  /\ pc[p] = "PoL6"
  /\ rVal' = [rVal EXCEPT ![p] = Mem[lh[p]].V]
  /\ Goto(p, "PoLFree")
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, valBag, nd, rh, lh, tmp, pushVal>>

PoL5(p) ==
  /\ pc[p] = "PoL5"
  /\ tmp' = [tmp EXCEPT ![p] = Mem[lh[p]].R]
  /\ Goto(p, "PoL7")
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, nd, rh, lh, pushVal>>

PoL7(p) ==  \* DCAS(&LeftHat, &lh->R, lh, lhR, lhR, lh)
  /\ pc[p] = "PoL7"
  /\ IF LeftHat = lh[p] /\ Mem[lh[p]].R = tmp[p]
       THEN /\ LeftHat' = tmp[p]
            /\ Mem' = [Mem EXCEPT ![lh[p]].R = lh[p]]
            /\ Goto(p, "PoL8")
       ELSE /\ Goto(p, "PoL1")
            /\ UNCHANGED <<LeftHat, Mem>>
  /\ UNCHANGED <<freeList, RightHat, rVal, valBag, nd, rh, lh, tmp, pushVal>>

PoL8(p) ==
  /\ pc[p] = "PoL8"
  /\ rVal' = [rVal EXCEPT ![p] = Mem[lh[p]].V]
  /\ Goto(p, "PoL9")
  /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, valBag, nd, rh, lh, tmp, pushVal>>

PoL9(p) ==
  /\ pc[p] = "PoL9"
  /\ Mem' = [Mem EXCEPT ![lh[p]].L = Dummy]
  /\ Goto(p, "PoLFree")
  /\ UNCHANGED <<freeList, LeftHat, RightHat, rVal, valBag, nd, rh, lh, tmp, pushVal>>

PoLFree(p) ==
  /\ pc[p] = "PoLFree"
  /\ IF GC THEN freeList' = freeList \cup {lh[p]}
           ELSE UNCHANGED freeList
  /\ Goto(p, "T2pop")
  /\ UNCHANGED <<Mem, LeftHat, RightHat, rVal, valBag, nd, rh, lh, tmp, pushVal>>

-----------------------------------------------------------------------------
Proc(p) ==
  \/ T1(p) \/ T2push(p) \/ T2pop(p)
  \/ PR1(p) \/ PR2(p) \/ PR3(p) \/ PR4(p) \/ PR5(p) \/ PR6(p) \/ PR7(p)
  \/ PL1(p) \/ PL2(p) \/ PL3(p) \/ PL4(p) \/ PL5(p) \/ PL6(p) \/ PL7(p)
  \/ PoR1(p) \/ PoR2(p) \/ PoR3(p) \/ PoR4(p) \/ PoR5(p) \/ PoR6(p)
  \/ PoR7(p) \/ PoR8(p) \/ PoR9(p) \/ PoRFree(p)
  \/ PoL1(p) \/ PoL2(p) \/ PoL3(p) \/ PoL4(p) \/ PoL5(p) \/ PoL6(p)
  \/ PoL7(p) \/ PoL8(p) \/ PoL9(p) \/ PoLFree(p)

Next == \E p \in Procs : Proc(p)

Spec == Init /\ [][Next]_vars

Liveness == \A p \in Procs : []<>(pc[p] = "T1")

Symmetry == Permutations(Address \ {Dummy}) \cup Permutations(Procs)

=============================================================================