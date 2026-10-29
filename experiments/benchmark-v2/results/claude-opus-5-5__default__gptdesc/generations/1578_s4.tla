---------------------------- MODULE DCASDeque ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Val,       \* values that can be pushed onto the deque
          Address,   \* allocatable node addresses
          Dummy,     \* address of the distinguished dummy node
          null,      \* null value / null pointer
          Procs      \* the set of test processes

ASSUME /\ Dummy \notin Address
       /\ null \notin (Address \cup {Dummy} \cup Val)
       /\ Procs # {}

Addr == Address \cup {Dummy}

Node == [L : Addr \cup {null}, R : Addr \cup {null}, V : Val \cup {null}]

VARIABLES mem,       \* memory: Addr -> Node
          LeftHat,   \* left end pointer
          RightHat,  \* right end pointer
          freeList,  \* set of free addresses
          valBag,    \* multiset (Val -> Nat) of values currently in the deque
          pc,        \* program counters
          nd, rh, rhR, lh, lhL, rhL, lhR, v, result   \* process-local variables

shared == <<mem, LeftHat, RightHat, freeList, valBag>>
locals == <<nd, rh, rhR, lh, lhL, rhL, lhR, v, result>>
vars   == <<mem, LeftHat, RightHat, freeList, valBag, pc,
            nd, rh, rhR, lh, lhL, rhL, lhR, v, result>>

Labels == {"T1",
           "PR1", "PR2", "PR3", "PR4", "PR5", "PR6", "PR7",
           "PL1", "PL2", "PL3", "PL4", "PL5", "PL6", "PL7",
           "OR1", "OR2", "OR3", "OR4", "OR5", "OR6", "OR7",
           "OL1", "OL2", "OL3", "OL4", "OL5", "OL6", "OL7"}

TypeOK ==
  /\ mem \in [Addr -> Node]
  /\ LeftHat \in Addr
  /\ RightHat \in Addr
  /\ freeList \subseteq Address
  /\ valBag \in [Val -> Nat]
  /\ pc \in [Procs -> Labels]
  /\ nd \in [Procs -> Addr \cup {null}]
  /\ rh \in [Procs -> Addr \cup {null}]
  /\ rhR \in [Procs -> Addr \cup {null}]
  /\ lh \in [Procs -> Addr \cup {null}]
  /\ lhL \in [Procs -> Addr \cup {null}]
  /\ rhL \in [Procs -> Addr \cup {null}]
  /\ lhR \in [Procs -> Addr \cup {null}]
  /\ v \in [Procs -> Val \cup {null}]
  /\ result \in [Procs -> Val \cup {null}]

Init ==
  /\ mem = [a \in Addr |-> IF a = Dummy
                             THEN [L |-> Dummy, R |-> Dummy, V |-> null]
                             ELSE [L |-> null, R |-> null, V |-> null]]
  /\ LeftHat = Dummy
  /\ RightHat = Dummy
  /\ freeList = Address
  /\ valBag = [x \in Val |-> 0]
  /\ pc = [p \in Procs |-> "T1"]
  /\ nd = [p \in Procs |-> null]
  /\ rh = [p \in Procs |-> null]
  /\ rhR = [p \in Procs |-> null]
  /\ lh = [p \in Procs |-> null]
  /\ lhL = [p \in Procs |-> null]
  /\ rhL = [p \in Procs |-> null]
  /\ lhR = [p \in Procs |-> null]
  /\ v = [p \in Procs |-> null]
  /\ result = [p \in Procs |-> null]

Goto(p, lbl) == pc' = [pc EXCEPT ![p] = lbl]

\* Returning a popped value: it must be in the bag
PopReturn(p, val) ==
  /\ Assert(val \in Val, "popped a non-value")
  /\ Assert(valBag[val] > 0, "popped value not in valBag")
  /\ valBag' = [valBag EXCEPT ![val] = @ - 1]

(***************************************************************************)
(* Test process: nondeterministically push or pop                         *)
(***************************************************************************)
T1(p) ==
  /\ pc[p] = "T1"
  /\ \/ \E x \in Val :
           /\ v' = [v EXCEPT ![p] = x]
           /\ \/ Goto(p, "PR1")
              \/ Goto(p, "PL1")
     \/ /\ \/ Goto(p, "OR1")
           \/ Goto(p, "OL1")
        /\ v' = v
  /\ UNCHANGED <<shared, nd, rh, rhR, lh, lhL, rhL, lhR, result>>

(***************************************************************************)
(* pushRight                                                               *)
(***************************************************************************)
PR1(p) ==
  /\ pc[p] = "PR1"
  /\ IF freeList = {}
       THEN /\ Goto(p, "T1")
            /\ UNCHANGED <<mem, freeList, nd>>
       ELSE \E a \in freeList :
              /\ nd' = [nd EXCEPT ![p] = a]
              /\ freeList' = freeList \ {a}
              /\ mem' = [mem EXCEPT ![a] = [L |-> Dummy, R |-> Dummy, V |-> v[p]]]
              /\ Goto(p, "PR2")
  /\ UNCHANGED <<LeftHat, RightHat, valBag, rh, rhR, lh, lhL, rhL, lhR, v, result>>

PR2(p) ==
  /\ pc[p] = "PR2"
  /\ rh' = [rh EXCEPT ![p] = RightHat]
  /\ Goto(p, "PR3")
  /\ UNCHANGED <<shared, nd, rhR, lh, lhL, rhL, lhR, v, result>>

PR3(p) ==
  /\ pc[p] = "PR3"
  /\ rhR' = [rhR EXCEPT ![p] = mem[rh[p]].R]
  /\ Goto(p, "PR4")
  /\ UNCHANGED <<shared, nd, rh, lh, lhL, rhL, lhR, v, result>>

PR4(p) ==
  /\ pc[p] = "PR4"
  /\ IF rhR[p] = rh[p]
       THEN /\ mem' = [mem EXCEPT ![nd[p]].L = Dummy]
            /\ Goto(p, "PR5")
       ELSE /\ mem' = [mem EXCEPT ![nd[p]].L = rh[p]]
            /\ Goto(p, "PR6")
  /\ UNCHANGED <<LeftHat, RightHat, freeList, valBag, locals>>

PR5(p) ==
  /\ pc[p] = "PR5"
  /\ lh' = [lh EXCEPT ![p] = LeftHat]
  /\ Goto(p, "PR7")
  /\ UNCHANGED <<shared, nd, rh, rhR, lhL, rhL, lhR, v, result>>

\* DCAS(&RightHat, &rh->R, rh, rhR, nd, nd)
PR6(p) ==
  /\ pc[p] = "PR6"
  /\ IF RightHat = rh[p] /\ mem[rh[p]].R = rhR[p]
       THEN /\ RightHat' = nd[p]
            /\ mem' = [mem EXCEPT ![rh[p]].R = nd[p]]
            /\ valBag' = [valBag EXCEPT ![v[p]] = @ + 1]
            /\ Goto(p, "T1")
       ELSE /\ Goto(p, "PR2")
            /\ UNCHANGED <<RightHat, mem, valBag>>
  /\ UNCHANGED <<LeftHat, freeList, locals>>

\* DCAS(&RightHat, &LeftHat, rh, lh, nd, nd)
PR7(p) ==
  /\ pc[p] = "PR7"
  /\ IF RightHat = rh[p] /\ LeftHat = lh[p]
       THEN /\ RightHat' = nd[p]
            /\ LeftHat' = nd[p]
            /\ valBag' = [valBag EXCEPT ![v[p]] = @ + 1]
            /\ Goto(p, "T1")
       ELSE /\ Goto(p, "PR2")
            /\ UNCHANGED <<RightHat, LeftHat, valBag>>
  /\ UNCHANGED <<mem, freeList, locals>>

(***************************************************************************)
(* pushLeft                                                                *)
(***************************************************************************)
PL1(p) ==
  /\ pc[p] = "PL1"
  /\ IF freeList = {}
       THEN /\ Goto(p, "T1")
            /\ UNCHANGED <<mem, freeList, nd>>
       ELSE \E a \in freeList :
              /\ nd' = [nd EXCEPT ![p] = a]
              /\ freeList' = freeList \ {a}
              /\ mem' = [mem EXCEPT ![a] = [L |-> Dummy, R |-> Dummy, V |-> v[p]]]
              /\ Goto(p, "PL2")
  /\ UNCHANGED <<LeftHat, RightHat, valBag, rh, rhR, lh, lhL, rhL, lhR, v, result>>

PL2(p) ==
  /\ pc[p] = "PL2"
  /\ lh' = [lh EXCEPT ![p] = LeftHat]
  /\ Goto(p, "PL3")
  /\ UNCHANGED <<shared, nd, rh, rhR, lhL, rhL, lhR, v, result>>

PL3(p) ==
  /\ pc[p] = "PL3"
  /\ lhL' = [lhL EXCEPT ![p] = mem[lh[p]].L]
  /\ Goto(p, "PL4")
  /\ UNCHANGED <<shared, nd, rh, rhR, lh, rhL, lhR, v, result>>

PL4(p) ==
  /\ pc[p] = "PL4"
  /\ IF lhL[p] = lh[p]
       THEN /\ mem' = [mem EXCEPT ![nd[p]].R = Dummy]
            /\ Goto(p, "PL5")
       ELSE /\ mem' = [mem EXCEPT ![nd[p]].R = lh[p]]
            /\ Goto(p, "PL6")
  /\ UNCHANGED <<LeftHat, RightHat, freeList, valBag, locals>>

PL5(p) ==
  /\ pc[p] = "PL5"
  /\ rh' = [rh EXCEPT ![p] = RightHat]
  /\ Goto(p, "PL7")
  /\ UNCHANGED <<shared, nd, rhR, lh, lhL, rhL, lhR, v, result>>

\* DCAS(&LeftHat, &lh->L, lh, lhL, nd, nd)
PL6(p) ==
  /\ pc[p] = "PL6"
  /\ IF LeftHat = lh[p] /\ mem[lh[p]].L = lhL[p]
       THEN /\ LeftHat' = nd[p]
            /\ mem' = [mem EXCEPT ![lh[p]].L = nd[p]]
            /\ valBag' = [valBag EXCEPT ![v[p]] = @ + 1]
            /\ Goto(p, "T1")
       ELSE /\ Goto(p, "PL2")
            /\ UNCHANGED <<LeftHat, mem, valBag>>
  /\ UNCHANGED <<RightHat, freeList, locals>>

\* DCAS(&LeftHat, &RightHat, lh, rh, nd, nd)
PL7(p) ==
  /\ pc[p] = "PL7"
  /\ IF LeftHat = lh[p] /\ RightHat = rh[p]
       THEN /\ LeftHat' = nd[p]
            /\ RightHat' = nd[p]
            /\ valBag' = [valBag EXCEPT ![v[p]] = @ + 1]
            /\ Goto(p, "T1")
       ELSE /\ Goto(p, "PL2")
            /\ UNCHANGED <<LeftHat, RightHat, valBag>>
  /\ UNCHANGED <<mem, freeList, locals>>

(***************************************************************************)
(* popRight                                                                *)
(***************************************************************************)
OR1(p) ==
  /\ pc[p] = "OR1"
  /\ rh' = [rh EXCEPT ![p] = RightHat]
  /\ Goto(p, "OR2")
  /\ UNCHANGED <<shared, nd, rhR, lh, lhL, rhL, lhR, v, result>>

OR2(p) ==
  /\ pc[p] = "OR2"
  /\ lh' = [lh EXCEPT ![p] = LeftHat]
  /\ Goto(p, "OR3")
  /\ UNCHANGED <<shared, nd, rh, rhR, lhL, rhL, lhR, v, result>>

OR3(p) ==
  /\ pc[p] = "OR3"
  /\ IF mem[rh[p]].R = rh[p]
       THEN Goto(p, "T1")                       \* return "empty"
       ELSE IF rh[p] = lh[p]
              THEN Goto(p, "OR4")
              ELSE Goto(p, "OR5")
  /\ UNCHANGED <<shared, locals>>

\* DCAS(&RightHat, &LeftHat, rh, lh, Dummy, Dummy)
OR4(p) ==
  /\ pc[p] = "OR4"
  /\ IF RightHat = rh[p] /\ LeftHat = lh[p]
       THEN /\ RightHat' = Dummy
            /\ LeftHat' = Dummy
            /\ result' = [result EXCEPT ![p] = mem[rh[p]].V]
            /\ PopReturn(p, mem[rh[p]].V)
            /\ Goto(p, "T1")
       ELSE /\ Goto(p, "OR1")
            /\ UNCHANGED <<RightHat, LeftHat, result, valBag>>
  /\ UNCHANGED <<mem, freeList, nd, rh, rhR, lh, lhL, rhL, lhR, v>>

OR5(p) ==
  /\ pc[p] = "OR5"
  /\ rhL' = [rhL EXCEPT ![p] = mem[rh[p]].L]
  /\ Goto(p, "OR6")
  /\ UNCHANGED <<shared, nd, rh, rhR, lh, lhL, lhR, v, result>>

\* DCAS(&RightHat, &rh->L, rh, rhL, rhL, rh)
OR6(p) ==
  /\ pc[p] = "OR6"
  /\ IF RightHat = rh[p] /\ mem[rh[p]].L = rhL[p]
       THEN /\ RightHat' = rhL[p]
            /\ mem' = [mem EXCEPT ![rh[p]].L = rh[p]]
            /\ result' = [result EXCEPT ![p] = mem[rh[p]].V]
            /\ Goto(p, "OR7")
       ELSE /\ Goto(p, "OR1")
            /\ UNCHANGED <<RightHat, mem, result>>
  /\ UNCHANGED <<LeftHat, freeList, valBag, nd, rh, rhR, lh, lhL, rhL, lhR, v>>

OR7(p) ==
  /\ pc[p] = "OR7"
  /\ mem' = [mem EXCEPT ![rh[p]].R = Dummy, ![rh[p]].V = null]
  /\ PopReturn(p, result[p])
  /\ Goto(p, "T1")
  /\ UNCHANGED <<LeftHat, RightHat, freeList, locals>>

(***************************************************************************)
(* popLeft                                                                 *)
(***************************************************************************)
OL1(p) ==
  /\ pc[p] = "OL1"
  /\ lh' = [lh EXCEPT ![p] = LeftHat]
  /\ Goto(p, "OL2")
  /\ UNCHANGED <<shared, nd, rh, rhR, lhL, rhL, lhR, v, result>>

OL2(p) ==
  /\ pc[p] = "OL2"
  /\ rh' = [rh EXCEPT ![p] = RightHat]
  /\ Goto(p, "OL3")
  /\ UNCHANGED <<shared, nd, rhR, lh, lhL, rhL, lhR, v, result>>

OL3(p) ==
  /\ pc[p] = "OL3"
  /\ IF mem[lh[p]].L = lh[p]
       THEN Goto(p, "T1")                       \* return "empty"
       ELSE IF lh[p] = rh[p]
              THEN Goto(p, "OL4")
              ELSE Goto(p, "OL5")
  /\ UNCHANGED <<shared, locals>>

\* DCAS(&LeftHat, &RightHat, lh, rh, Dummy, Dummy)
OL4(p) ==
  /\ pc[p] = "OL4"
  /\ IF LeftHat = lh[p] /\ RightHat = rh[p]
       THEN /\ LeftHat' = Dummy
            /\ RightHat' = Dummy
            /\ result' = [result EXCEPT ![p] = mem[lh[p]].V]
            /\ PopReturn(p, mem[lh[p]].V)
            /\ Goto(p, "T1")
       ELSE /\ Goto(p, "OL1")
            /\ UNCHANGED <<LeftHat, RightHat, result, valBag>>
  /\ UNCHANGED <<mem, freeList, nd, rh, rhR, lh, lhL, rhL, lhR, v>>

OL5(p) ==
  /\ pc[p] = "OL5"
  /\ lhR' = [lhR EXCEPT ![p] = mem[lh[p]].R]
  /\ Goto(p, "OL6")
  /\ UNCHANGED <<shared, nd, rh, rhR, lh, lhL, rhL, v, result>>

\* DCAS(&LeftHat, &lh->R, lh, lhR, lhR, lh)
OL6(p) ==
  /\ pc[p] = "OL6"
  /\ IF LeftHat = lh[p] /\ mem[lh[p]].R = lhR[p]
       THEN /\ LeftHat' = lhR[p]
            /\ mem' = [mem EXCEPT ![lh[p]].R = lh[p]]
            /\ result' = [result EXCEPT ![p] = mem[lh[p]].V]
            /\ Goto(p, "OL7")
       ELSE /\ Goto(p, "OL1")
            /\ UNCHANGED <<LeftHat, mem, result>>
  /\ UNCHANGED <<RightHat, freeList, valBag, nd, rh, rhR, lh, lhL, rhL, lhR, v>>

OL7(p) ==
  /\ pc[p] = "OL7"
  /\ mem' = [mem EXCEPT ![lh[p]].L = Dummy, ![lh[p]].V = null]
  /\ PopReturn(p, result[p])
  /\ Goto(p, "T1")
  /\ UNCHANGED <<LeftHat, RightHat, freeList, locals>>

(***************************************************************************)
(* Garbage collection: return unreachable nodes to the freelist            *)
(***************************************************************************)
Roots ==
  ({LeftHat, RightHat}
     \cup UNION {{nd[p], rh[p], rhR[p], lh[p], lhL[p], rhL[p], lhR[p]} : p \in Procs})
  \cap Addr

RECURSIVE Reach(_)
Reach(S) ==
  LET T == S \cup (({mem[a].L : a \in S} \cup {mem[a].R : a \in S}) \cap Addr)
  IN  IF T = S THEN S ELSE Reach(T)

Garbage == Address \ (Reach(Roots) \cup freeList)

GC ==
  /\ Garbage # {}
  /\ freeList' = freeList \cup Garbage
  /\ UNCHANGED <<mem, LeftHat, RightHat, valBag, pc, locals>>

(***************************************************************************)
(* Process and system                                                      *)
(***************************************************************************)
Proc(p) ==
  \/ T1(p)
  \/ PR1(p) \/ PR2(p) \/ PR3(p) \/ PR4(p) \/ PR5(p) \/ PR6(p) \/ PR7(p)
  \/ PL1(p) \/ PL2(p) \/ PL3(p) \/ PL4(p) \/ PL5(p) \/ PL6(p) \/ PL7(p)
  \/ OR1(p) \/ OR2(p) \/ OR3(p) \/ OR4(p) \/ OR5(p) \/ OR6(p) \/ OR7(p)
  \/ OL1(p) \/ OL2(p) \/ OL3(p) \/ OL4(p) \/ OL5(p) \/ OL6(p) \/ OL7(p)

Next == GC \/ (\E p \in Procs : Proc(p))

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A p \in Procs : WF_vars(Proc(p))
        /\ WF_vars(GC)

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
HatsValid == /\ LeftHat \in Addr
             /\ RightHat \in Addr
             /\ LeftHat \notin freeList
             /\ RightHat \notin freeList

DummyIntact == mem[Dummy] = [L |-> Dummy, R |-> Dummy, V |-> null]

Liveness == \A p \in Procs : []<>(pc[p] = "T1")

THEOREM Spec => [](TypeOK /\ HatsValid /\ DummyIntact)
THEOREM Spec => Liveness
=============================================================================