---------------------------- MODULE SnarkDeque ----------------------------
(***************************************************************************)
(* A concurrent double-ended queue in the style of Detlefs et al.          *)
(* ("Snark"). The shared pointers are updated with DCAS (double            *)
(* compare-and-swap), modeled here as single atomic steps that check and   *)
(* update two locations together. Each test process repeatedly and         *)
(* nondeterministically calls pushLeft, pushRight, popLeft or popRight.    *)
(* The variable valBag is a multiset of the values currently in the        *)
(* deque. It is used to assert that every popped value was previously      *)
(* pushed and has not already been popped.                                 *)
(* This is the TLA+ translation of the corresponding PlusCal algorithm.    *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANTS Val,      \* values that can be pushed
          Address,  \* memory addresses
          Dummy,    \* the address of the dummy (sentinel) node
          null,     \* null pointer / null value
          Procs     \* the test processes

ASSUME /\ Dummy \in Address
       /\ null \notin Address
       /\ null \notin Val
       /\ Procs # {}

Ptr    == Address \cup {null}
Node   == [L : Ptr, R : Ptr, V : Val \cup {null}]
Result == Val \cup {"okay", "full", "empty", null}

VARIABLES mem,       \* Address -> node record
          LeftHat,   \* left end pointer
          RightHat,  \* right end pointer
          freeList,  \* set of unallocated addresses
          valBag,    \* multiset of values currently in the deque
          pc,        \* per-process program counter
          nd, rh, lh, rhR, lhL, rhL, lhR, pval, result  \* per-process locals

vars == << mem, LeftHat, RightHat, freeList, valBag, pc,
           nd, rh, lh, rhR, lhL, rhL, lhR, pval, result >>

ProcSet == Procs

Init ==
  /\ mem = [a \in Address |->
              IF a = Dummy THEN [L |-> Dummy, R |-> Dummy, V |-> null]
                           ELSE [L |-> null, R |-> null, V |-> null]]
  /\ LeftHat = Dummy
  /\ RightHat = Dummy
  /\ freeList = Address \ {Dummy}
  /\ valBag = [v \in Val |-> 0]
  /\ pc = [self \in ProcSet |-> "T1"]
  /\ nd = [self \in ProcSet |-> null]
  /\ rh = [self \in ProcSet |-> null]
  /\ lh = [self \in ProcSet |-> null]
  /\ rhR = [self \in ProcSet |-> null]
  /\ lhL = [self \in ProcSet |-> null]
  /\ rhL = [self \in ProcSet |-> null]
  /\ lhR = [self \in ProcSet |-> null]
  /\ pval = [self \in ProcSet |-> null]
  /\ result = [self \in ProcSet |-> null]

(***************************************************************************)
(* Test process: pick an operation nondeterministically                    *)
(***************************************************************************)
T1(self) ==
  /\ pc[self] = "T1"
  /\ \/ \E v \in Val :
           /\ pval' = [pval EXCEPT ![self] = v]
           /\ pc' = [pc EXCEPT ![self] = "PL1"]
     \/ \E v \in Val :
           /\ pval' = [pval EXCEPT ![self] = v]
           /\ pc' = [pc EXCEPT ![self] = "PR1"]
     \/ /\ pc' = [pc EXCEPT ![self] = "PoL1"]
        /\ UNCHANGED pval
     \/ /\ pc' = [pc EXCEPT ![self] = "PoR1"]
        /\ UNCHANGED pval
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                  nd, rh, lh, rhR, lhL, rhL, lhR, result >>

(***************************************************************************)
(* pushRight                                                               *)
(***************************************************************************)
PR1(self) ==
  /\ pc[self] = "PR1"
  /\ IF freeList = {}
       THEN /\ result' = [result EXCEPT ![self] = "full"]
            /\ pc' = [pc EXCEPT ![self] = "T1"]
            /\ UNCHANGED << mem, freeList, nd >>
       ELSE \E a \in freeList :
              /\ nd' = [nd EXCEPT ![self] = a]
              /\ freeList' = freeList \ {a}
              /\ mem' = [mem EXCEPT ![a] = [L |-> null, R |-> Dummy, V |-> pval[self]]]
              /\ pc' = [pc EXCEPT ![self] = "PR2"]
              /\ UNCHANGED result
  /\ UNCHANGED << LeftHat, RightHat, valBag, rh, lh, rhR, lhL, rhL, lhR, pval >>

PR2(self) ==
  /\ pc[self] = "PR2"
  /\ rh' = [rh EXCEPT ![self] = RightHat]
  /\ pc' = [pc EXCEPT ![self] = "PR3"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                  nd, lh, rhR, lhL, rhL, lhR, pval, result >>

PR3(self) ==
  /\ pc[self] = "PR3"
  /\ rhR' = [rhR EXCEPT ![self] = mem[rh[self]].R]
  /\ pc' = [pc EXCEPT ![self] = "PR4"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                  nd, rh, lh, lhL, rhL, lhR, pval, result >>

PR4(self) ==
  /\ pc[self] = "PR4"
  /\ IF rhR[self] = rh[self]
       THEN /\ mem' = [mem EXCEPT ![nd[self]].L = Dummy]
            /\ pc' = [pc EXCEPT ![self] = "PR5"]
       ELSE /\ mem' = [mem EXCEPT ![nd[self]].L = rh[self]]
            /\ pc' = [pc EXCEPT ![self] = "PR6"]
  /\ UNCHANGED << LeftHat, RightHat, freeList, valBag,
                  nd, rh, lh, rhR, lhL, rhL, lhR, pval, result >>

PR5(self) ==
  /\ pc[self] = "PR5"
  /\ lh' = [lh EXCEPT ![self] = LeftHat]
  /\ pc' = [pc EXCEPT ![self] = "PR7"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                  nd, rh, rhR, lhL, rhL, lhR, pval, result >>

\* DCAS(&RightHat, &LeftHat, rh, lh, nd, nd)
PR7(self) ==
  /\ pc[self] = "PR7"
  /\ IF RightHat = rh[self] /\ LeftHat = lh[self]
       THEN /\ RightHat' = nd[self]
            /\ LeftHat' = nd[self]
            /\ valBag' = [valBag EXCEPT ![pval[self]] = @ + 1]
            /\ result' = [result EXCEPT ![self] = "okay"]
            /\ pc' = [pc EXCEPT ![self] = "T1"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "PR2"]
            /\ UNCHANGED << RightHat, LeftHat, valBag, result >>
  /\ UNCHANGED << mem, freeList, nd, rh, lh, rhR, lhL, rhL, lhR, pval >>

\* DCAS(&RightHat, &rh->R, rh, rhR, nd, nd)
PR6(self) ==
  /\ pc[self] = "PR6"
  /\ IF RightHat = rh[self] /\ mem[rh[self]].R = rhR[self]
       THEN /\ RightHat' = nd[self]
            /\ mem' = [mem EXCEPT ![rh[self]].R = nd[self]]
            /\ valBag' = [valBag EXCEPT ![pval[self]] = @ + 1]
            /\ result' = [result EXCEPT ![self] = "okay"]
            /\ pc' = [pc EXCEPT ![self] = "T1"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "PR2"]
            /\ UNCHANGED << RightHat, mem, valBag, result >>
  /\ UNCHANGED << LeftHat, freeList, nd, rh, lh, rhR, lhL, rhL, lhR, pval >>

(***************************************************************************)
(* pushLeft                                                                *)
(***************************************************************************)
PL1(self) ==
  /\ pc[self] = "PL1"
  /\ IF freeList = {}
       THEN /\ result' = [result EXCEPT ![self] = "full"]
            /\ pc' = [pc EXCEPT ![self] = "T1"]
            /\ UNCHANGED << mem, freeList, nd >>
       ELSE \E a \in freeList :
              /\ nd' = [nd EXCEPT ![self] = a]
              /\ freeList' = freeList \ {a}
              /\ mem' = [mem EXCEPT ![a] = [L |-> Dummy, R |-> null, V |-> pval[self]]]
              /\ pc' = [pc EXCEPT ![self] = "PL2"]
              /\ UNCHANGED result
  /\ UNCHANGED << LeftHat, RightHat, valBag, rh, lh, rhR, lhL, rhL, lhR, pval >>

PL2(self) ==
  /\ pc[self] = "PL2"
  /\ lh' = [lh EXCEPT ![self] = LeftHat]
  /\ pc' = [pc EXCEPT ![self] = "PL3"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                  nd, rh, rhR, lhL, rhL, lhR, pval, result >>

PL3(self) ==
  /\ pc[self] = "PL3"
  /\ lhL' = [lhL EXCEPT ![self] = mem[lh[self]].L]
  /\ pc' = [pc EXCEPT ![self] = "PL4"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                  nd, rh, lh, rhR, rhL, lhR, pval, result >>

PL4(self) ==
  /\ pc[self] = "PL4"
  /\ IF lhL[self] = lh[self]
       THEN /\ mem' = [mem EXCEPT ![nd[self]].R = Dummy]
            /\ pc' = [pc EXCEPT ![self] = "PL5"]
       ELSE /\ mem' = [mem EXCEPT ![nd[self]].R = lh[self]]
            /\ pc' = [pc EXCEPT ![self] = "PL6"]
  /\ UNCHANGED << LeftHat, RightHat, freeList, valBag,
                  nd, rh, lh, rhR, lhL, rhL, lhR, pval, result >>

PL5(self) ==
  /\ pc[self] = "PL5"
  /\ rh' = [rh EXCEPT ![self] = RightHat]
  /\ pc' = [pc EXCEPT ![self] = "PL7"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                  nd, lh, rhR, lhL, rhL, lhR, pval, result >>

\* DCAS(&LeftHat, &RightHat, lh, rh, nd, nd)
PL7(self) ==
  /\ pc[self] = "PL7"
  /\ IF LeftHat = lh[self] /\ RightHat = rh[self]
       THEN /\ LeftHat' = nd[self]
            /\ RightHat' = nd[self]
            /\ valBag' = [valBag EXCEPT ![pval[self]] = @ + 1]
            /\ result' = [result EXCEPT ![self] = "okay"]
            /\ pc' = [pc EXCEPT ![self] = "T1"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "PL2"]
            /\ UNCHANGED << RightHat, LeftHat, valBag, result >>
  /\ UNCHANGED << mem, freeList, nd, rh, lh, rhR, lhL, rhL, lhR, pval >>

\* DCAS(&LeftHat, &lh->L, lh, lhL, nd, nd)
PL6(self) ==
  /\ pc[self] = "PL6"
  /\ IF LeftHat = lh[self] /\ mem[lh[self]].L = lhL[self]
       THEN /\ LeftHat' = nd[self]
            /\ mem' = [mem EXCEPT ![lh[self]].L = nd[self]]
            /\ valBag' = [valBag EXCEPT ![pval[self]] = @ + 1]
            /\ result' = [result EXCEPT ![self] = "okay"]
            /\ pc' = [pc EXCEPT ![self] = "T1"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "PL2"]
            /\ UNCHANGED << LeftHat, mem, valBag, result >>
  /\ UNCHANGED << RightHat, freeList, nd, rh, lh, rhR, lhL, rhL, lhR, pval >>

(***************************************************************************)
(* popRight                                                                *)
(***************************************************************************)
PoR1(self) ==
  /\ pc[self] = "PoR1"
  /\ rh' = [rh EXCEPT ![self] = RightHat]
  /\ pc' = [pc EXCEPT ![self] = "PoR2"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                  nd, lh, rhR, lhL, rhL, lhR, pval, result >>

PoR2(self) ==
  /\ pc[self] = "PoR2"
  /\ lh' = [lh EXCEPT ![self] = LeftHat]
  /\ pc' = [pc EXCEPT ![self] = "PoR3"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                  nd, rh, rhR, lhL, rhL, lhR, pval, result >>

PoR3(self) ==
  /\ pc[self] = "PoR3"
  /\ IF mem[rh[self]].R = rh[self]
       THEN /\ result' = [result EXCEPT ![self] = "empty"]
            /\ pc' = [pc EXCEPT ![self] = "T1"]
       ELSE /\ IF rh[self] = lh[self]
                 THEN pc' = [pc EXCEPT ![self] = "PoR4"]
                 ELSE pc' = [pc EXCEPT ![self] = "PoR5"]
            /\ UNCHANGED result
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                  nd, rh, lh, rhR, lhL, rhL, lhR, pval >>

\* DCAS(&RightHat, &LeftHat, rh, lh, Dummy, Dummy)
PoR4(self) ==
  /\ pc[self] = "PoR4"
  /\ IF RightHat = rh[self] /\ LeftHat = lh[self]
       THEN LET v == mem[rh[self]].V IN
            /\ Assert(v \in Val /\ valBag[v] > 0,
                      "popRight returned a value not in the deque")
            /\ RightHat' = Dummy
            /\ LeftHat' = Dummy
            /\ valBag' = IF v \in Val THEN [valBag EXCEPT ![v] = @ - 1]
                                      ELSE valBag
            /\ result' = [result EXCEPT ![self] = v]
            /\ pc' = [pc EXCEPT ![self] = "T1"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "PoR1"]
            /\ UNCHANGED << RightHat, LeftHat, valBag, result >>
  /\ UNCHANGED << mem, freeList, nd, rh, lh, rhR, lhL, rhL, lhR, pval >>

PoR5(self) ==
  /\ pc[self] = "PoR5"
  /\ rhL' = [rhL EXCEPT ![self] = mem[rh[self]].L]
  /\ pc' = [pc EXCEPT ![self] = "PoR6"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                  nd, rh, lh, rhR, lhL, lhR, pval, result >>

\* DCAS(&RightHat, &rh->L, rh, rhL, rhL, rh)
PoR6(self) ==
  /\ pc[self] = "PoR6"
  /\ IF RightHat = rh[self] /\ mem[rh[self]].L = rhL[self]
       THEN LET v == mem[rh[self]].V IN
            /\ Assert(v \in Val /\ valBag[v] > 0,
                      "popRight returned a value not in the deque")
            /\ RightHat' = rhL[self]
            /\ mem' = [mem EXCEPT ![rh[self]].L = rh[self]]
            /\ valBag' = IF v \in Val THEN [valBag EXCEPT ![v] = @ - 1]
                                      ELSE valBag
            /\ result' = [result EXCEPT ![self] = v]
            /\ pc' = [pc EXCEPT ![self] = "T1"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "PoR1"]
            /\ UNCHANGED << RightHat, mem, valBag, result >>
  /\ UNCHANGED << LeftHat, freeList, nd, rh, lh, rhR, lhL, rhL, lhR, pval >>

(***************************************************************************)
(* popLeft                                                                 *)
(***************************************************************************)
PoL1(self) ==
  /\ pc[self] = "PoL1"
  /\ lh' = [lh EXCEPT ![self] = LeftHat]
  /\ pc' = [pc EXCEPT ![self] = "PoL2"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                  nd, rh, rhR, lhL, rhL, lhR, pval, result >>

PoL2(self) ==
  /\ pc[self] = "PoL2"
  /\ rh' = [rh EXCEPT ![self] = RightHat]
  /\ pc' = [pc EXCEPT ![self] = "PoL3"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                  nd, lh, rhR, lhL, rhL, lhR, pval, result >>

PoL3(self) ==
  /\ pc[self] = "PoL3"
  /\ IF mem[lh[self]].L = lh[self]
       THEN /\ result' = [result EXCEPT ![self] = "empty"]
            /\ pc' = [pc EXCEPT ![self] = "T1"]
       ELSE /\ IF lh[self] = rh[self]
                 THEN pc' = [pc EXCEPT ![self] = "PoL4"]
                 ELSE pc' = [pc EXCEPT ![self] = "PoL5"]
            /\ UNCHANGED result
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                  nd, rh, lh, rhR, lhL, rhL, lhR, pval >>

\* DCAS(&LeftHat, &RightHat, lh, rh, Dummy, Dummy)
PoL4(self) ==
  /\ pc[self] = "PoL4"
  /\ IF LeftHat = lh[self] /\ RightHat = rh[self]
       THEN LET v == mem[lh[self]].V IN
            /\ Assert(v \in Val /\ valBag[v] > 0,
                      "popLeft returned a value not in the deque")
            /\ LeftHat' = Dummy
            /\ RightHat' = Dummy
            /\ valBag' = IF v \in Val THEN [valBag EXCEPT ![v] = @ - 1]
                                      ELSE valBag
            /\ result' = [result EXCEPT ![self] = v]
            /\ pc' = [pc EXCEPT ![self] = "T1"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "PoL1"]
            /\ UNCHANGED << RightHat, LeftHat, valBag, result >>
  /\ UNCHANGED << mem, freeList, nd, rh, lh, rhR, lhL, rhL, lhR, pval >>

PoL5(self) ==
  /\ pc[self] = "PoL5"
  /\ lhR' = [lhR EXCEPT ![self] = mem[lh[self]].R]
  /\ pc' = [pc EXCEPT ![self] = "PoL6"]
  /\ UNCHANGED << mem, LeftHat, RightHat, freeList, valBag,
                  nd, rh, lh, rhR, lhL, rhL, pval, result >>

\* DCAS(&LeftHat, &lh->R, lh, lhR, lhR, lh)
PoL6(self) ==
  /\ pc[self] = "PoL6"
  /\ IF LeftHat = lh[self] /\ mem[lh[self]].R = lhR[self]
       THEN LET v == mem[lh[self]].V IN
            /\ Assert(v \in Val /\ valBag[v] > 0,
                      "popLeft returned a value not in the deque")
            /\ LeftHat' = lhR[self]
            /\ mem' = [mem EXCEPT ![lh[self]].R = lh[self]]
            /\ valBag' = IF v \in Val THEN [valBag EXCEPT ![v] = @ - 1]
                                      ELSE valBag
            /\ result' = [result EXCEPT ![self] = v]
            /\ pc' = [pc EXCEPT ![self] = "T1"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "PoL1"]
            /\ UNCHANGED << LeftHat, mem, valBag, result >>
  /\ UNCHANGED << RightHat, freeList, nd, rh, lh, rhR, lhL, rhL, lhR, pval >>

(***************************************************************************)
(* Process and system definitions                                          *)
(***************************************************************************)
proc(self) ==
  \/ T1(self)
  \/ PR1(self) \/ PR2(self) \/ PR3(self) \/ PR4(self)
  \/ PR5(self) \/ PR6(self) \/ PR7(self)
  \/ PL1(self) \/ PL2(self) \/ PL3(self) \/ PL4(self)
  \/ PL5(self) \/ PL6(self) \/ PL7(self)
  \/ PoR1(self) \/ PoR2(self) \/ PoR3(self)
  \/ PoR4(self) \/ PoR5(self) \/ PoR6(self)
  \/ PoL1(self) \/ PoL2(self) \/ PoL3(self)
  \/ PoL4(self) \/ PoL5(self) \/ PoL6(self)

Next == \E self \in Procs : proc(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(proc(self))

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
Labels == {"T1",
           "PR1", "PR2", "PR3", "PR4", "PR5", "PR6", "PR7",
           "PL1", "PL2", "PL3", "PL4", "PL5", "PL6", "PL7",
           "PoR1", "PoR2", "PoR3", "PoR4", "PoR5", "PoR6",
           "PoL1", "PoL2", "PoL3", "PoL4", "PoL5", "PoL6"}

TypeOK ==
  /\ mem \in [Address -> Node]
  /\ LeftHat \in Address
  /\ RightHat \in Address
  /\ freeList \subseteq Address \ {Dummy}
  /\ valBag \in [Val -> Nat]
  /\ pc \in [ProcSet -> Labels]
  /\ nd \in [ProcSet -> Ptr]
  /\ rh \in [ProcSet -> Ptr]
  /\ lh \in [ProcSet -> Ptr]
  /\ rhR \in [ProcSet -> Ptr]
  /\ lhL \in [ProcSet -> Ptr]
  /\ rhL \in [ProcSet -> Ptr]
  /\ lhR \in [ProcSet -> Ptr]
  /\ pval \in [ProcSet -> Val \cup {null}]
  /\ result \in [ProcSet -> Result]

\* The dummy node always points to itself on both sides.
DummyInv == mem[Dummy].L = Dummy /\ mem[Dummy].R = Dummy

\* Liveness: every test process returns to T1 infinitely often.
Liveness == \A self \in Procs : []<>(pc[self] = "T1")

THEOREM Spec => [](TypeOK /\ DummyInv)
THEOREM Spec => Liveness
=============================================================================