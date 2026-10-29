--------------------------- MODULE DetlefsDeque ---------------------------
EXTENDS Naturals, TLC

CONSTANTS Val,      \* values that may be pushed onto the deque
          Address,  \* allocatable node addresses
          Dummy,    \* address of the distinguished Dummy node
          null,     \* null value
          Procs     \* set of test processes

ASSUME /\ Dummy \notin Address
       /\ null \notin Val
       /\ {"okay", "empty", "full"} \cap Val = {}

Node == [L : Address \cup {Dummy}, R : Address \cup {Dummy}, V : Val \cup {null}]

(***************************************************************************
--algorithm DetlefsDeque (abridged; translation below)
  variables mem, LeftHat, RightHat, freeList, valBag;
  process test \in Procs
    T1: either push(Left/Right) or pop(Left/Right)
    T2: check valBag consistency; goto T1
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES mem, LeftHat, RightHat, freeList, valBag, pc,
          nd, rh, lh, rhR, rhL, lhL, lhR, v, result

vars == << mem, LeftHat, RightHat, freeList, valBag, pc,
           nd, rh, lh, rhR, rhL, lhL, lhR, v, result >>

locals == << nd, rh, lh, rhR, rhL, lhL, lhR, v, result >>

Init == /\ mem = [a \in Address \cup {Dummy} |->
                    [L |-> Dummy, R |-> Dummy, V |-> null]]
        /\ LeftHat = Dummy
        /\ RightHat = Dummy
        /\ freeList = Address
        /\ valBag = [x \in Val |-> 0]
        /\ nd = [p \in Procs |-> Dummy]
        /\ rh = [p \in Procs |-> Dummy]
        /\ lh = [p \in Procs |-> Dummy]
        /\ rhR = [p \in Procs |-> Dummy]
        /\ rhL = [p \in Procs |-> Dummy]
        /\ lhL = [p \in Procs |-> Dummy]
        /\ lhR = [p \in Procs |-> Dummy]
        /\ v = [p \in Procs |-> null]
        /\ result = [p \in Procs |-> null]
        /\ pc = [p \in Procs |-> "T1"]

(***************************************************************************)
(* Test process top-level control                                          *)
(***************************************************************************)
T1(self) == /\ pc[self] = "T1"
            /\ \/ \E val \in Val :
                    /\ v' = [v EXCEPT ![self] = val]
                    /\ valBag' = [valBag EXCEPT ![val] = @ + 1]
                    /\ pc' = [pc EXCEPT ![self] = "PR1"]
               \/ \E val \in Val :
                    /\ v' = [v EXCEPT ![self] = val]
                    /\ valBag' = [valBag EXCEPT ![val] = @ + 1]
                    /\ pc' = [pc EXCEPT ![self] = "PL1"]
               \/ /\ pc' = [pc EXCEPT ![self] = "QR1"]
                  /\ UNCHANGED << v, valBag >>
               \/ /\ pc' = [pc EXCEPT ![self] = "QL1"]
                  /\ UNCHANGED << v, valBag >>
            /\ UNCHANGED << mem, LeftHat, RightHat, freeList,
                            nd, rh, lh, rhR, rhL, lhL, lhR, result >>

T2(self) == /\ pc[self] = "T2"
            /\ IF result[self] \in Val
                 THEN /\ Assert(valBag[result[self]] > 0,
                                "Failure of assertion at T2: popped value not in valBag")
                      /\ valBag' = [valBag EXCEPT ![result[self]] = @ - 1]
                 ELSE IF result[self] = "full"
                        THEN valBag' = [valBag EXCEPT ![v[self]] = @ - 1]
                        ELSE UNCHANGED valBag
            /\ pc' = [pc EXCEPT ![self] = "T1"]
            /\ UNCHANGED << mem, LeftHat, RightHat, freeList, locals >>

(***************************************************************************)
(* pushRight                                                               *)
(***************************************************************************)
PR1(self) == /\ pc[self] = "PR1"
             /\ IF freeList = {}
                  THEN /\ result' = [result EXCEPT ![self] = "full"]
                       /\ pc' = [pc EXCEPT ![self] = "T2"]
                       /\ UNCHANGED << mem, freeList, nd >>
                  ELSE /\ \E a \in freeList :
                            /\ nd' = [nd EXCEPT ![self] = a]
                            /\ freeList' = freeList \ {a}
                            /\ mem' = [mem EXCEPT ![a] =
                                         [L |-> Dummy, R |-> Dummy, V |-> v[self]]]
                       /\ pc' = [pc EXCEPT ![self] = "PR2"]
                       /\ UNCHANGED result
             /\ UNCHANGED << LeftHat, RightHat, valBag,
                             rh, lh, rhR, rhL, lhL, lhR, v >>

PR2(self) == /\ pc[self] = "PR2"
             /\ rh' = [rh EXCEPT ![self] = RightHat]
             /\ pc' = [pc EXCEPT ![self] = "PR3"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                             nd, lh, rhR, rhL, lhL, lhR, v, result >>

PR3(self) == /\ pc[self] = "PR3"
             /\ rhR' = [rhR EXCEPT ![self] = mem[rh[self]].R]
             /\ pc' = [pc EXCEPT ![self] = "PR4"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                             nd, rh, lh, rhL, lhL, lhR, v, result >>

PR4(self) == /\ pc[self] = "PR4"
             /\ IF rhR[self] = rh[self]
                  THEN /\ mem' = [mem EXCEPT ![nd[self]].L = Dummy]
                       /\ pc' = [pc EXCEPT ![self] = "PR5"]
                  ELSE /\ mem' = [mem EXCEPT ![nd[self]].L = rh[self]]
                       /\ pc' = [pc EXCEPT ![self] = "PR6"]
             /\ UNCHANGED << LeftHat, RightHat, freeList, valBag, locals >>

PR5(self) == /\ pc[self] = "PR5"
             /\ lh' = [lh EXCEPT ![self] = LeftHat]
             /\ pc' = [pc EXCEPT ![self] = "PR7"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                             nd, rh, rhR, rhL, lhL, lhR, v, result >>

\* DCAS(&RightHat, &LeftHat, rh, lh, nd, nd)
PR7(self) == /\ pc[self] = "PR7"
             /\ IF RightHat = rh[self] /\ LeftHat = lh[self]
                  THEN /\ RightHat' = nd[self]
                       /\ LeftHat' = nd[self]
                       /\ result' = [result EXCEPT ![self] = "okay"]
                       /\ pc' = [pc EXCEPT ![self] = "T2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "PR2"]
                       /\ UNCHANGED << RightHat, LeftHat, result >>
             /\ UNCHANGED << mem, freeList, valBag,
                             nd, rh, lh, rhR, rhL, lhL, lhR, v >>

\* DCAS(&RightHat, &rh->R, rh, rhR, nd, nd)
PR6(self) == /\ pc[self] = "PR6"
             /\ IF RightHat = rh[self] /\ mem[rh[self]].R = rhR[self]
                  THEN /\ RightHat' = nd[self]
                       /\ mem' = [mem EXCEPT ![rh[self]].R = nd[self]]
                       /\ result' = [result EXCEPT ![self] = "okay"]
                       /\ pc' = [pc EXCEPT ![self] = "T2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "PR2"]
                       /\ UNCHANGED << RightHat, mem, result >>
             /\ UNCHANGED << LeftHat, freeList, valBag,
                             nd, rh, lh, rhR, rhL, lhL, lhR, v >>

(***************************************************************************)
(* pushLeft                                                                *)
(***************************************************************************)
PL1(self) == /\ pc[self] = "PL1"
             /\ IF freeList = {}
                  THEN /\ result' = [result EXCEPT ![self] = "full"]
                       /\ pc' = [pc EXCEPT ![self] = "T2"]
                       /\ UNCHANGED << mem, freeList, nd >>
                  ELSE /\ \E a \in freeList :
                            /\ nd' = [nd EXCEPT ![self] = a]
                            /\ freeList' = freeList \ {a}
                            /\ mem' = [mem EXCEPT ![a] =
                                         [L |-> Dummy, R |-> Dummy, V |-> v[self]]]
                       /\ pc' = [pc EXCEPT ![self] = "PL2"]
                       /\ UNCHANGED result
             /\ UNCHANGED << LeftHat, RightHat, valBag,
                             rh, lh, rhR, rhL, lhL, lhR, v >>

PL2(self) == /\ pc[self] = "PL2"
             /\ lh' = [lh EXCEPT ![self] = LeftHat]
             /\ pc' = [pc EXCEPT ![self] = "PL3"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                             nd, rh, rhR, rhL, lhL, lhR, v, result >>

PL3(self) == /\ pc[self] = "PL3"
             /\ lhL' = [lhL EXCEPT ![self] = mem[lh[self]].L]
             /\ pc' = [pc EXCEPT ![self] = "PL4"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                             nd, rh, lh, rhR, rhL, lhR, v, result >>

PL4(self) == /\ pc[self] = "PL4"
             /\ IF lhL[self] = lh[self]
                  THEN /\ mem' = [mem EXCEPT ![nd[self]].R = Dummy]
                       /\ pc' = [pc EXCEPT ![self] = "PL5"]
                  ELSE /\ mem' = [mem EXCEPT ![nd[self]].R = lh[self]]
                       /\ pc' = [pc EXCEPT ![self] = "PL6"]
             /\ UNCHANGED << LeftHat, RightHat, freeList, valBag, locals >>

PL5(self) == /\ pc[self] = "PL5"
             /\ rh' = [rh EXCEPT ![self] = RightHat]
             /\ pc' = [pc EXCEPT ![self] = "PL7"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                             nd, lh, rhR, rhL, lhL, lhR, v, result >>

\* DCAS(&LeftHat, &RightHat, lh, rh, nd, nd)
PL7(self) == /\ pc[self] = "PL7"
             /\ IF LeftHat = lh[self] /\ RightHat = rh[self]
                  THEN /\ LeftHat' = nd[self]
                       /\ RightHat' = nd[self]
                       /\ result' = [result EXCEPT ![self] = "okay"]
                       /\ pc' = [pc EXCEPT ![self] = "T2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "PL2"]
                       /\ UNCHANGED << RightHat, LeftHat, result >>
             /\ UNCHANGED << mem, freeList, valBag,
                             nd, rh, lh, rhR, rhL, lhL, lhR, v >>

\* DCAS(&LeftHat, &lh->L, lh, lhL, nd, nd)
PL6(self) == /\ pc[self] = "PL6"
             /\ IF LeftHat = lh[self] /\ mem[lh[self]].L = lhL[self]
                  THEN /\ LeftHat' = nd[self]
                       /\ mem' = [mem EXCEPT ![lh[self]].L = nd[self]]
                       /\ result' = [result EXCEPT ![self] = "okay"]
                       /\ pc' = [pc EXCEPT ![self] = "T2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "PL2"]
                       /\ UNCHANGED << LeftHat, mem, result >>
             /\ UNCHANGED << RightHat, freeList, valBag,
                             nd, rh, lh, rhR, rhL, lhL, lhR, v >>

(***************************************************************************)
(* popRight                                                                *)
(***************************************************************************)
QR1(self) == /\ pc[self] = "QR1"
             /\ rh' = [rh EXCEPT ![self] = RightHat]
             /\ pc' = [pc EXCEPT ![self] = "QR2"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                             nd, lh, rhR, rhL, lhL, lhR, v, result >>

QR2(self) == /\ pc[self] = "QR2"
             /\ lh' = [lh EXCEPT ![self] = LeftHat]
             /\ pc' = [pc EXCEPT ![self] = "QR3"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                             nd, rh, rhR, rhL, lhL, lhR, v, result >>

QR3(self) == /\ pc[self] = "QR3"
             /\ IF mem[rh[self]].R = rh[self]
                  THEN /\ result' = [result EXCEPT ![self] = "empty"]
                       /\ pc' = [pc EXCEPT ![self] = "T2"]
                  ELSE /\ IF rh[self] = lh[self]
                            THEN pc' = [pc EXCEPT ![self] = "QR4"]
                            ELSE pc' = [pc EXCEPT ![self] = "QR5"]
                       /\ UNCHANGED result
             /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                             nd, rh, lh, rhR, rhL, lhL, lhR, v >>

\* DCAS(&RightHat, &LeftHat, rh, lh, Dummy, Dummy)
QR4(self) == /\ pc[self] = "QR4"
             /\ IF RightHat = rh[self] /\ LeftHat = lh[self]
                  THEN /\ RightHat' = Dummy
                       /\ LeftHat' = Dummy
                       /\ pc' = [pc EXCEPT ![self] = "QR8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "QR1"]
                       /\ UNCHANGED << RightHat, LeftHat >>
             /\ UNCHANGED << mem, freeList, valBag, locals >>

QR8(self) == /\ pc[self] = "QR8"
             /\ result' = [result EXCEPT ![self] = mem[rh[self]].V]
             /\ pc' = [pc EXCEPT ![self] = "T2"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                             nd, rh, lh, rhR, rhL, lhL, lhR, v >>

QR5(self) == /\ pc[self] = "QR5"
             /\ rhL' = [rhL EXCEPT ![self] = mem[rh[self]].L]
             /\ pc' = [pc EXCEPT ![self] = "QR6"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                             nd, rh, lh, rhR, lhL, lhR, v, result >>

\* DCAS(&RightHat, &rh->L, rh, rhL, rhL, rh)
QR6(self) == /\ pc[self] = "QR6"
             /\ IF RightHat = rh[self] /\ mem[rh[self]].L = rhL[self]
                  THEN /\ RightHat' = rhL[self]
                       /\ mem' = [mem EXCEPT ![rh[self]].L = rh[self]]
                       /\ pc' = [pc EXCEPT ![self] = "QR7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "QR1"]
                       /\ UNCHANGED << RightHat, mem >>
             /\ UNCHANGED << LeftHat, freeList, valBag, locals >>

QR7(self) == /\ pc[self] = "QR7"
             /\ result' = [result EXCEPT ![self] = mem[rh[self]].V]
             /\ mem' = [mem EXCEPT ![rh[self]].R = Dummy]
             /\ pc' = [pc EXCEPT ![self] = "T2"]
             /\ UNCHANGED << LeftHat, RightHat, freeList, valBag,
                             nd, rh, lh, rhR, rhL, lhL, lhR, v >>

(***************************************************************************)
(* popLeft                                                                 *)
(***************************************************************************)
QL1(self) == /\ pc[self] = "QL1"
             /\ lh' = [lh EXCEPT ![self] = LeftHat]
             /\ pc' = [pc EXCEPT ![self] = "QL2"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                             nd, rh, rhR, rhL, lhL, lhR, v, result >>

QL2(self) == /\ pc[self] = "QL2"
             /\ rh' = [rh EXCEPT ![self] = RightHat]
             /\ pc' = [pc EXCEPT ![self] = "QL3"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                             nd, lh, rhR, rhL, lhL, lhR, v, result >>

QL3(self) == /\ pc[self] = "QL3"
             /\ IF mem[lh[self]].L = lh[self]
                  THEN /\ result' = [result EXCEPT ![self] = "empty"]
                       /\ pc' = [pc EXCEPT ![self] = "T2"]
                  ELSE /\ IF lh[self] = rh[self]
                            THEN pc' = [pc EXCEPT ![self] = "QL4"]
                            ELSE pc' = [pc EXCEPT ![self] = "QL5"]
                       /\ UNCHANGED result
             /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                             nd, rh, lh, rhR, rhL, lhL, lhR, v >>

\* DCAS(&LeftHat, &RightHat, lh, rh, Dummy, Dummy)
QL4(self) == /\ pc[self] = "QL4"
             /\ IF LeftHat = lh[self] /\ RightHat = rh[self]
                  THEN /\ LeftHat' = Dummy
                       /\ RightHat' = Dummy
                       /\ pc' = [pc EXCEPT ![self] = "QL8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "QL1"]
                       /\ UNCHANGED << RightHat, LeftHat >>
             /\ UNCHANGED << mem, freeList, valBag, locals >>

QL8(self) == /\ pc[self] = "QL8"
             /\ result' = [result EXCEPT ![self] = mem[lh[self]].V]
             /\ pc' = [pc EXCEPT ![self] = "T2"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                             nd, rh, lh, rhR, rhL, lhL, lhR, v >>

QL5(self) == /\ pc[self] = "QL5"
             /\ lhR' = [lhR EXCEPT ![self] = mem[lh[self]].R]
             /\ pc' = [pc EXCEPT ![self] = "QL6"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                             nd, rh, lh, rhR, rhL, lhL, v, result >>

\* DCAS(&LeftHat, &lh->R, lh, lhR, lhR, lh)
QL6(self) == /\ pc[self] = "QL6"
             /\ IF LeftHat = lh[self] /\ mem[lh[self]].R = lhR[self]
                  THEN /\ LeftHat' = lhR[self]
                       /\ mem' = [mem EXCEPT ![lh[self]].R = lh[self]]
                       /\ pc' = [pc EXCEPT ![self] = "QL7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "QL1"]
                       /\ UNCHANGED << LeftHat, mem >>
             /\ UNCHANGED << RightHat, freeList, valBag, locals >>

QL7(self) == /\ pc[self] = "QL7"
             /\ result' = [result EXCEPT ![self] = mem[lh[self]].V]
             /\ mem' = [mem EXCEPT ![lh[self]].L = Dummy]
             /\ pc' = [pc EXCEPT ![self] = "T2"]
             /\ UNCHANGED << LeftHat, RightHat, freeList, valBag,
                             nd, rh, lh, rhR, rhL, lhL, lhR, v >>

test(self) == \/ T1(self) \/ T2(self)
              \/ PR1(self) \/ PR2(self) \/ PR3(self) \/ PR4(self)
              \/ PR5(self) \/ PR6(self) \/ PR7(self)
              \/ PL1(self) \/ PL2(self) \/ PL3(self) \/ PL4(self)
              \/ PL5(self) \/ PL6(self) \/ PL7(self)
              \/ QR1(self) \/ QR2(self) \/ QR3(self) \/ QR4(self)
              \/ QR5(self) \/ QR6(self) \/ QR7(self) \/ QR8(self)
              \/ QL1(self) \/ QL2(self) \/ QL3(self) \/ QL4(self)
              \/ QL5(self) \/ QL6(self) \/ QL7(self) \/ QL8(self)

Next == \E self \in Procs : test(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(test(self))
\* END TRANSLATION

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
Ptr == Address \cup {Dummy}

TypeOK == /\ mem \in [Ptr -> Node]
          /\ LeftHat \in Ptr
          /\ RightHat \in Ptr
          /\ freeList \subseteq Address
          /\ valBag \in [Val -> Nat]
          /\ nd \in [Procs -> Ptr]
          /\ rh \in [Procs -> Ptr]
          /\ lh \in [Procs -> Ptr]
          /\ rhR \in [Procs -> Ptr]
          /\ rhL \in [Procs -> Ptr]
          /\ lhL \in [Procs -> Ptr]
          /\ lhR \in [Procs -> Ptr]
          /\ v \in [Procs -> Val \cup {null}]
          /\ result \in [Procs -> Val \cup {null, "okay", "empty", "full"}]

\* Every value popped must previously have been pushed and not yet popped
ValBagConsistent ==
    \A p \in Procs : (pc[p] = "T2" /\ result[p] \in Val) => valBag[result[p]] > 0

\* Liveness: every test process returns to T1 infinitely often
Liveness == \A p \in Procs : []<>(pc[p] = "T1")

THEOREM Spec => [](TypeOK /\ ValBagConsistent)
THEOREM Spec => Liveness
=============================================================================