------------------------------ MODULE DetlefsDeque ------------------------------
(***************************************************************************)
(* A concurrent double-ended queue in the style of Detlefs et al.          *)
(* ("Snark").  Each DCAS is modelled as one atomic step that compares and  *)
(* updates two shared locations together.  Every other memory access is a  *)
(* separate step.  This is written in the style of a PlusCal translation.  *)
(*                                                                         *)
(* Shared state:                                                           *)
(*   mem      : Addresses -> node records [R, L, V]                        *)
(*   LeftHat  : pointer to the left end                                    *)
(*   RightHat : pointer to the right end                                   *)
(*   freeList : set of unallocated addresses                               *)
(*   valBag   : multiset (bag) of values currently in the deque            *)
(*                                                                         *)
(* Each test process repeatedly and nondeterministically runs pushLeft,    *)
(* pushRight, popLeft or popRight.  It then updates and checks valBag.     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Val,       \* set of values that can be pushed
          Address,   \* set of allocatable node addresses
          Dummy,     \* the address of the dummy (sentinel) node
          Procs,     \* set of test process identifiers
          null       \* a value that is not an address and not a value

ASSUME Dummy \notin Address
ASSUME null \notin (Address \cup {Dummy} \cup Val)

Addresses == Address \cup {Dummy}

Node == [R : Addresses \cup {null}, L : Addresses \cup {null}, V : Val \cup {null}]

NullNode == [R |-> null, L |-> null, V |-> null]

Results == Val \cup {"okay", "full", "empty", null}

Ops == {"pushL", "pushR", "popL", "popR"}

VARIABLES mem, LeftHat, RightHat, freeList, valBag,
          pc, op, arg, result,
          nd, rh, lh, rhR, lhL, rhL, lhR

vars == << mem, LeftHat, RightHat, freeList, valBag,
           pc, op, arg, result, nd, rh, lh, rhR, lhL, rhL, lhR >>

-----------------------------------------------------------------------------
Init ==
  /\ mem = [a \in Addresses |->
              IF a = Dummy THEN [R |-> Dummy, L |-> Dummy, V |-> null]
                           ELSE NullNode]
  /\ LeftHat = Dummy
  /\ RightHat = Dummy
  /\ freeList = Address
  /\ valBag = [x \in Val |-> 0]
  /\ pc = [p \in Procs |-> "T1"]
  /\ op = [p \in Procs |-> null]
  /\ arg = [p \in Procs |-> null]
  /\ result = [p \in Procs |-> null]
  /\ nd = [p \in Procs |-> null]
  /\ rh = [p \in Procs |-> null]
  /\ lh = [p \in Procs |-> null]
  /\ rhR = [p \in Procs |-> null]
  /\ lhL = [p \in Procs |-> null]
  /\ rhL = [p \in Procs |-> null]
  /\ lhR = [p \in Procs |-> null]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Test process                                                            *)
(***************************************************************************)
T1(self) ==
  /\ pc[self] = "T1"
  /\ \E o \in Ops, x \in Val :
       /\ op' = [op EXCEPT ![self] = o]
       /\ arg' = [arg EXCEPT ![self] = x]
       /\ pc' = [pc EXCEPT ![self] =
                   CASE o = "pushL" -> "PL1"
                     [] o = "pushR" -> "PR1"
                     [] o = "popL"  -> "OL1"
                     [] OTHER       -> "OR1"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, result,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

T2(self) ==
  /\ pc[self] = "T2"
  /\ IF op[self] \in {"pushL", "pushR"}
       THEN valBag' = IF result[self] = "okay"
                        THEN [valBag EXCEPT ![arg[self]] = @ + 1]
                        ELSE valBag
       ELSE IF result[self] \in Val
              THEN /\ Assert(valBag[result[self]] > 0,
                             "Popped a value that is not in the deque")
                   /\ valBag' = [valBag EXCEPT ![result[self]] = @ - 1]
              ELSE valBag' = valBag
  /\ pc' = [pc EXCEPT ![self] = "T1"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, op, arg, result,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

-----------------------------------------------------------------------------
(***************************************************************************)
(* pushRight                                                               *)
(***************************************************************************)
PR1(self) ==
  /\ pc[self] = "PR1"
  /\ IF freeList = {}
       THEN /\ result' = [result EXCEPT ![self] = "full"]
            /\ pc' = [pc EXCEPT ![self] = "T2"]
            /\ UNCHANGED << mem, freeList, nd >>
       ELSE \E a \in freeList :
              /\ nd' = [nd EXCEPT ![self] = a]
              /\ freeList' = freeList \ {a}
              /\ mem' = [mem EXCEPT ![a] = [R |-> Dummy, L |-> null, V |-> arg[self]]]
              /\ pc' = [pc EXCEPT ![self] = "PR2"]
              /\ result' = result
  /\ UNCHANGED << LeftHat, RightHat, valBag, op, arg,
                  rh, lh, rhR, lhL, rhL, lhR >>

PR2(self) ==
  /\ pc[self] = "PR2"
  /\ rh' = [rh EXCEPT ![self] = RightHat]
  /\ pc' = [pc EXCEPT ![self] = "PR3"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, op, arg, result,
                  nd, lh, rhR, lhL, rhL, lhR >>

PR3(self) ==
  /\ pc[self] = "PR3"
  /\ rhR' = [rhR EXCEPT ![self] = mem[rh[self]].R]
  /\ pc' = [pc EXCEPT ![self] = "PR4"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, op, arg, result,
                  nd, rh, lh, lhL, rhL, lhR >>

PR4(self) ==
  /\ pc[self] = "PR4"
  /\ IF rhR[self] = rh[self]
       THEN /\ mem' = [mem EXCEPT ![nd[self]].L = Dummy]
            /\ pc' = [pc EXCEPT ![self] = "PR5"]
       ELSE /\ mem' = [mem EXCEPT ![nd[self]].L = rh[self]]
            /\ pc' = [pc EXCEPT ![self] = "PR7"]
  /\ UNCHANGED << LeftHat, RightHat, freeList, valBag, op, arg, result,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

PR5(self) ==
  /\ pc[self] = "PR5"
  /\ lh' = [lh EXCEPT ![self] = LeftHat]
  /\ pc' = [pc EXCEPT ![self] = "PR6"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, op, arg, result,
                  nd, rh, rhR, lhL, rhL, lhR >>

\* DCAS(&RightHat, &LeftHat, rh, lh, nd, nd)
PR6(self) ==
  /\ pc[self] = "PR6"
  /\ IF RightHat = rh[self] /\ LeftHat = lh[self]
       THEN /\ RightHat' = nd[self]
            /\ LeftHat' = nd[self]
            /\ result' = [result EXCEPT ![self] = "okay"]
            /\ pc' = [pc EXCEPT ![self] = "T2"]
       ELSE /\ UNCHANGED << RightHat, LeftHat, result >>
            /\ pc' = [pc EXCEPT ![self] = "PR2"]
  /\ UNCHANGED << mem, freeList, valBag, op, arg,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

\* DCAS(&RightHat, &rh->R, rh, rhR, nd, nd)
PR7(self) ==
  /\ pc[self] = "PR7"
  /\ IF RightHat = rh[self] /\ mem[rh[self]].R = rhR[self]
       THEN /\ RightHat' = nd[self]
            /\ mem' = [mem EXCEPT ![rh[self]].R = nd[self]]
            /\ result' = [result EXCEPT ![self] = "okay"]
            /\ pc' = [pc EXCEPT ![self] = "T2"]
       ELSE /\ UNCHANGED << RightHat, mem, result >>
            /\ pc' = [pc EXCEPT ![self] = "PR2"]
  /\ UNCHANGED << LeftHat, freeList, valBag, op, arg,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

pushRight(self) == PR1(self) \/ PR2(self) \/ PR3(self) \/ PR4(self)
                   \/ PR5(self) \/ PR6(self) \/ PR7(self)

-----------------------------------------------------------------------------
(***************************************************************************)
(* pushLeft                                                                *)
(***************************************************************************)
PL1(self) ==
  /\ pc[self] = "PL1"
  /\ IF freeList = {}
       THEN /\ result' = [result EXCEPT ![self] = "full"]
            /\ pc' = [pc EXCEPT ![self] = "T2"]
            /\ UNCHANGED << mem, freeList, nd >>
       ELSE \E a \in freeList :
              /\ nd' = [nd EXCEPT ![self] = a]
              /\ freeList' = freeList \ {a}
              /\ mem' = [mem EXCEPT ![a] = [R |-> null, L |-> Dummy, V |-> arg[self]]]
              /\ pc' = [pc EXCEPT ![self] = "PL2"]
              /\ result' = result
  /\ UNCHANGED << LeftHat, RightHat, valBag, op, arg,
                  rh, lh, rhR, lhL, rhL, lhR >>

PL2(self) ==
  /\ pc[self] = "PL2"
  /\ lh' = [lh EXCEPT ![self] = LeftHat]
  /\ pc' = [pc EXCEPT ![self] = "PL3"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, op, arg, result,
                  nd, rh, rhR, lhL, rhL, lhR >>

PL3(self) ==
  /\ pc[self] = "PL3"
  /\ lhL' = [lhL EXCEPT ![self] = mem[lh[self]].L]
  /\ pc' = [pc EXCEPT ![self] = "PL4"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, op, arg, result,
                  nd, rh, lh, rhR, rhL, lhR >>

PL4(self) ==
  /\ pc[self] = "PL4"
  /\ IF lhL[self] = lh[self]
       THEN /\ mem' = [mem EXCEPT ![nd[self]].R = Dummy]
            /\ pc' = [pc EXCEPT ![self] = "PL5"]
       ELSE /\ mem' = [mem EXCEPT ![nd[self]].R = lh[self]]
            /\ pc' = [pc EXCEPT ![self] = "PL7"]
  /\ UNCHANGED << LeftHat, RightHat, freeList, valBag, op, arg, result,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

PL5(self) ==
  /\ pc[self] = "PL5"
  /\ rh' = [rh EXCEPT ![self] = RightHat]
  /\ pc' = [pc EXCEPT ![self] = "PL6"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, op, arg, result,
                  nd, lh, rhR, lhL, rhL, lhR >>

\* DCAS(&LeftHat, &RightHat, lh, rh, nd, nd)
PL6(self) ==
  /\ pc[self] = "PL6"
  /\ IF LeftHat = lh[self] /\ RightHat = rh[self]
       THEN /\ LeftHat' = nd[self]
            /\ RightHat' = nd[self]
            /\ result' = [result EXCEPT ![self] = "okay"]
            /\ pc' = [pc EXCEPT ![self] = "T2"]
       ELSE /\ UNCHANGED << LeftHat, RightHat, result >>
            /\ pc' = [pc EXCEPT ![self] = "PL2"]
  /\ UNCHANGED << mem, freeList, valBag, op, arg,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

\* DCAS(&LeftHat, &lh->L, lh, lhL, nd, nd)
PL7(self) ==
  /\ pc[self] = "PL7"
  /\ IF LeftHat = lh[self] /\ mem[lh[self]].L = lhL[self]
       THEN /\ LeftHat' = nd[self]
            /\ mem' = [mem EXCEPT ![lh[self]].L = nd[self]]
            /\ result' = [result EXCEPT ![self] = "okay"]
            /\ pc' = [pc EXCEPT ![self] = "T2"]
       ELSE /\ UNCHANGED << LeftHat, mem, result >>
            /\ pc' = [pc EXCEPT ![self] = "PL2"]
  /\ UNCHANGED << RightHat, freeList, valBag, op, arg,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

pushLeft(self) == PL1(self) \/ PL2(self) \/ PL3(self) \/ PL4(self)
                  \/ PL5(self) \/ PL6(self) \/ PL7(self)

-----------------------------------------------------------------------------
(***************************************************************************)
(* popRight                                                                *)
(***************************************************************************)
OR1(self) ==
  /\ pc[self] = "OR1"
  /\ rh' = [rh EXCEPT ![self] = RightHat]
  /\ pc' = [pc EXCEPT ![self] = "OR2"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, op, arg, result,
                  nd, lh, rhR, lhL, rhL, lhR >>

OR2(self) ==
  /\ pc[self] = "OR2"
  /\ lh' = [lh EXCEPT ![self] = LeftHat]
  /\ pc' = [pc EXCEPT ![self] = "OR3"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, op, arg, result,
                  nd, rh, rhR, lhL, rhL, lhR >>

OR3(self) ==
  /\ pc[self] = "OR3"
  /\ IF mem[rh[self]].R = rh[self]
       THEN /\ result' = [result EXCEPT ![self] = "empty"]
            /\ pc' = [pc EXCEPT ![self] = "T2"]
       ELSE /\ result' = result
            /\ IF rh[self] = lh[self]
                 THEN pc' = [pc EXCEPT ![self] = "OR4"]
                 ELSE pc' = [pc EXCEPT ![self] = "OR5"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, op, arg,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

\* DCAS(&RightHat, &LeftHat, rh, lh, Dummy, Dummy)
OR4(self) ==
  /\ pc[self] = "OR4"
  /\ IF RightHat = rh[self] /\ LeftHat = lh[self]
       THEN /\ RightHat' = Dummy
            /\ LeftHat' = Dummy
            /\ pc' = [pc EXCEPT ![self] = "OR4b"]
       ELSE /\ UNCHANGED << RightHat, LeftHat >>
            /\ pc' = [pc EXCEPT ![self] = "OR1"]
  /\ UNCHANGED << mem, freeList, valBag, op, arg, result,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

OR4b(self) ==
  /\ pc[self] = "OR4b"
  /\ result' = [result EXCEPT ![self] = mem[rh[self]].V]
  /\ pc' = [pc EXCEPT ![self] = "T2"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, op, arg,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

OR5(self) ==
  /\ pc[self] = "OR5"
  /\ rhL' = [rhL EXCEPT ![self] = mem[rh[self]].L]
  /\ pc' = [pc EXCEPT ![self] = "OR6"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, op, arg, result,
                  nd, rh, lh, rhR, lhL, lhR >>

\* DCAS(&RightHat, &rh->L, rh, rhL, rhL, rh)
OR6(self) ==
  /\ pc[self] = "OR6"
  /\ IF RightHat = rh[self] /\ mem[rh[self]].L = rhL[self]
       THEN /\ RightHat' = rhL[self]
            /\ mem' = [mem EXCEPT ![rh[self]].L = rh[self]]
            /\ pc' = [pc EXCEPT ![self] = "OR7"]
       ELSE /\ UNCHANGED << RightHat, mem >>
            /\ pc' = [pc EXCEPT ![self] = "OR1"]
  /\ UNCHANGED << LeftHat, freeList, valBag, op, arg, result,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

OR7(self) ==
  /\ pc[self] = "OR7"
  /\ result' = [result EXCEPT ![self] = mem[rh[self]].V]
  /\ pc' = [pc EXCEPT ![self] = "OR8"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, op, arg,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

OR8(self) ==
  /\ pc[self] = "OR8"
  /\ mem' = [mem EXCEPT ![rh[self]].R = Dummy]
  /\ pc' = [pc EXCEPT ![self] = "T2"]
  /\ UNCHANGED << LeftHat, RightHat, freeList, valBag, op, arg, result,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

popRight(self) == OR1(self) \/ OR2(self) \/ OR3(self) \/ OR4(self)
                  \/ OR4b(self) \/ OR5(self) \/ OR6(self) \/ OR7(self)
                  \/ OR8(self)

-----------------------------------------------------------------------------
(***************************************************************************)
(* popLeft                                                                 *)
(***************************************************************************)
OL1(self) ==
  /\ pc[self] = "OL1"
  /\ lh' = [lh EXCEPT ![self] = LeftHat]
  /\ pc' = [pc EXCEPT ![self] = "OL2"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, op, arg, result,
                  nd, rh, rhR, lhL, rhL, lhR >>

OL2(self) ==
  /\ pc[self] = "OL2"
  /\ rh' = [rh EXCEPT ![self] = RightHat]
  /\ pc' = [pc EXCEPT ![self] = "OL3"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, op, arg, result,
                  nd, lh, rhR, lhL, rhL, lhR >>

OL3(self) ==
  /\ pc[self] = "OL3"
  /\ IF mem[lh[self]].L = lh[self]
       THEN /\ result' = [result EXCEPT ![self] = "empty"]
            /\ pc' = [pc EXCEPT ![self] = "T2"]
       ELSE /\ result' = result
            /\ IF lh[self] = rh[self]
                 THEN pc' = [pc EXCEPT ![self] = "OL4"]
                 ELSE pc' = [pc EXCEPT ![self] = "OL5"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, op, arg,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

\* DCAS(&LeftHat, &RightHat, lh, rh, Dummy, Dummy)
OL4(self) ==
  /\ pc[self] = "OL4"
  /\ IF LeftHat = lh[self] /\ RightHat = rh[self]
       THEN /\ LeftHat' = Dummy
            /\ RightHat' = Dummy
            /\ pc' = [pc EXCEPT ![self] = "OL4b"]
       ELSE /\ UNCHANGED << LeftHat, RightHat >>
            /\ pc' = [pc EXCEPT ![self] = "OL1"]
  /\ UNCHANGED << mem, freeList, valBag, op, arg, result,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

OL4b(self) ==
  /\ pc[self] = "OL4b"
  /\ result' = [result EXCEPT ![self] = mem[lh[self]].V]
  /\ pc' = [pc EXCEPT ![self] = "T2"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, op, arg,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

OL5(self) ==
  /\ pc[self] = "OL5"
  /\ lhR' = [lhR EXCEPT ![self] = mem[lh[self]].R]
  /\ pc' = [pc EXCEPT ![self] = "OL6"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, op, arg, result,
                  nd, rh, lh, rhR, lhL, rhL >>

\* DCAS(&LeftHat, &lh->R, lh, lhR, lhR, lh)
OL6(self) ==
  /\ pc[self] = "OL6"
  /\ IF LeftHat = lh[self] /\ mem[lh[self]].R = lhR[self]
       THEN /\ LeftHat' = lhR[self]
            /\ mem' = [mem EXCEPT ![lh[self]].R = lh[self]]
            /\ pc' = [pc EXCEPT ![self] = "OL7"]
       ELSE /\ UNCHANGED << LeftHat, mem >>
            /\ pc' = [pc EXCEPT ![self] = "OL1"]
  /\ UNCHANGED << RightHat, freeList, valBag, op, arg, result,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

OL7(self) ==
  /\ pc[self] = "OL7"
  /\ result' = [result EXCEPT ![self] = mem[lh[self]].V]
  /\ pc' = [pc EXCEPT ![self] = "OL8"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag, op, arg,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

OL8(self) ==
  /\ pc[self] = "OL8"
  /\ mem' = [mem EXCEPT ![lh[self]].L = Dummy]
  /\ pc' = [pc EXCEPT ![self] = "T2"]
  /\ UNCHANGED << LeftHat, RightHat, freeList, valBag, op, arg, result,
                  nd, rh, lh, rhR, lhL, rhL, lhR >>

popLeft(self) == OL1(self) \/ OL2(self) \/ OL3(self) \/ OL4(self)
                 \/ OL4b(self) \/ OL5(self) \/ OL6(self) \/ OL7(self)
                 \/ OL8(self)

-----------------------------------------------------------------------------
test(self) == T1(self) \/ T2(self)
              \/ pushRight(self) \/ pushLeft(self)
              \/ popRight(self) \/ popLeft(self)

Next == \E self \in Procs : test(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(test(self))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
Labels == {"T1", "T2",
           "PR1", "PR2", "PR3", "PR4", "PR5", "PR6", "PR7",
           "PL1", "PL2", "PL3", "PL4", "PL5", "PL6", "PL7",
           "OR1", "OR2", "OR3", "OR4", "OR4b", "OR5", "OR6", "OR7", "OR8",
           "OL1", "OL2", "OL3", "OL4", "OL4b", "OL5", "OL6", "OL7", "OL8"}

PtrOrNull == Addresses \cup {null}

TypeOK ==
  /\ mem \in [Addresses -> Node]
  /\ LeftHat \in Addresses
  /\ RightHat \in Addresses
  /\ freeList \subseteq Address
  /\ valBag \in [Val -> Nat]
  /\ pc \in [Procs -> Labels]
  /\ op \in [Procs -> Ops \cup {null}]
  /\ arg \in [Procs -> Val \cup {null}]
  /\ result \in [Procs -> Results]
  /\ nd \in [Procs -> PtrOrNull]
  /\ rh \in [Procs -> PtrOrNull]
  /\ lh \in [Procs -> PtrOrNull]
  /\ rhR \in [Procs -> PtrOrNull]
  /\ lhL \in [Procs -> PtrOrNull]
  /\ rhL \in [Procs -> PtrOrNull]
  /\ lhR \in [Procs -> PtrOrNull]

\* The dummy node is never allocated from the free list.
DummyNotFree == Dummy \notin freeList

\* The bag of values never goes negative. Each pop returns a pushed value.
ValBagOK == \A x \in Val : valBag[x] >= 0

\* The number of values in the bag never exceeds the number of
\* allocated nodes.
BagBounded ==
  LET RECURSIVE Sum(_)
      Sum(S) == IF S = {} THEN 0
                ELSE LET x == CHOOSE y \in S : TRUE
                     IN  valBag[x] + Sum(S \ {x})
  IN  Sum(Val) <= Cardinality(Address \ freeList)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness: every test process returns to T1 infinitely often.            *)
(***************************************************************************)
Liveness == \A p \in Procs : []<>(pc[p] = "T1")

THEOREM Spec => [](TypeOK /\ DummyNotFree /\ ValBagOK)
THEOREM Spec => Liveness
=============================================================================