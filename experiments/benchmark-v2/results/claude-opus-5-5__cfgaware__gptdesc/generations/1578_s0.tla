------------------------------ MODULE DCASDeque ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Val, Address, Dummy, Procs, null, GC, defaultInitValue

ASSUME /\ Dummy \in Address
       /\ null \notin Address
       /\ null \notin Val
       /\ defaultInitValue \notin Address
       /\ GC \in BOOLEAN

(***************************************************************************)
(* Translation of the PlusCal algorithm.                                   *)
(***************************************************************************)
VARIABLES mem, freeList, LeftHat, RightHat, valBag, pc,
          nd, rh, rhR, rhL, lh, lhL, lhR, retVal, pushVal

vars == << mem, freeList, LeftHat, RightHat, valBag, pc,
           nd, rh, rhR, rhL, lh, lhL, lhR, retVal, pushVal >>

locals == << nd, rh, rhR, rhL, lh, lhL, lhR, retVal, pushVal >>

Node == [L : Address \cup {null}, R : Address \cup {null}, V : Val \cup {null}]

Init ==
  /\ mem = [a \in Address |->
              IF a = Dummy THEN [L |-> Dummy, R |-> Dummy, V |-> null]
                           ELSE [L |-> null, R |-> null, V |-> null]]
  /\ freeList = Address \ {Dummy}
  /\ LeftHat = Dummy
  /\ RightHat = Dummy
  /\ valBag = [v \in Val |-> 0]
  /\ pc = [p \in Procs |-> "T1"]
  /\ nd = [p \in Procs |-> defaultInitValue]
  /\ rh = [p \in Procs |-> defaultInitValue]
  /\ rhR = [p \in Procs |-> defaultInitValue]
  /\ rhL = [p \in Procs |-> defaultInitValue]
  /\ lh = [p \in Procs |-> defaultInitValue]
  /\ lhL = [p \in Procs |-> defaultInitValue]
  /\ lhR = [p \in Procs |-> defaultInitValue]
  /\ retVal = [p \in Procs |-> defaultInitValue]
  /\ pushVal = [p \in Procs |-> defaultInitValue]

(*************************** Test process ***********************************)
T1(self) ==
  /\ pc[self] = "T1"
  /\ \/ \E v \in Val :
          /\ pushVal' = [pushVal EXCEPT ![self] = v]
          /\ \/ pc' = [pc EXCEPT ![self] = "PR1"]
             \/ pc' = [pc EXCEPT ![self] = "PL1"]
     \/ /\ pc' = [pc EXCEPT ![self] = "OR1"]
        /\ UNCHANGED pushVal
     \/ /\ pc' = [pc EXCEPT ![self] = "OL1"]
        /\ UNCHANGED pushVal
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rh, rhR, rhL, lh, lhL, lhR, retVal >>

T2(self) ==
  /\ pc[self] = "T2"
  /\ IF retVal[self] = "okay"
       THEN valBag' = [valBag EXCEPT ![pushVal[self]] = @ + 1]
       ELSE UNCHANGED valBag
  /\ pc' = [pc EXCEPT ![self] = "T1"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, locals >>

T3(self) ==
  /\ pc[self] = "T3"
  /\ IF retVal[self] \in Val
       THEN /\ Assert(valBag[retVal[self]] > 0,
                      "Failure of assertion: popped value not in valBag")
            /\ valBag' = [valBag EXCEPT ![retVal[self]] = @ - 1]
       ELSE /\ Assert(retVal[self] = "empty",
                      "Failure of assertion: bad pop result")
            /\ UNCHANGED valBag
  /\ pc' = [pc EXCEPT ![self] = "T1"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, locals >>

(*************************** pushRight **************************************)
PR1(self) ==
  /\ pc[self] = "PR1"
  /\ IF freeList = {}
       THEN /\ retVal' = [retVal EXCEPT ![self] = "full"]
            /\ pc' = [pc EXCEPT ![self] = "T2"]
            /\ UNCHANGED << mem, freeList, nd >>
       ELSE \E a \in freeList :
              /\ nd' = [nd EXCEPT ![self] = a]
              /\ freeList' = freeList \ {a}
              /\ mem' = [mem EXCEPT ![a] = [L |-> null, R |-> Dummy,
                                            V |-> pushVal[self]]]
              /\ pc' = [pc EXCEPT ![self] = "PR2"]
              /\ UNCHANGED retVal
  /\ UNCHANGED << LeftHat, RightHat, valBag, rh, rhR, rhL, lh, lhL, lhR, pushVal >>

PR2(self) ==
  /\ pc[self] = "PR2"
  /\ rh' = [rh EXCEPT ![self] = RightHat]
  /\ pc' = [pc EXCEPT ![self] = "PR3"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rhR, rhL, lh, lhL, lhR, retVal, pushVal >>

PR3(self) ==
  /\ pc[self] = "PR3"
  /\ rhR' = [rhR EXCEPT ![self] = mem[rh[self]].R]
  /\ pc' = [pc EXCEPT ![self] = "PR4"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rh, rhL, lh, lhL, lhR, retVal, pushVal >>

PR4(self) ==
  /\ pc[self] = "PR4"
  /\ IF rhR[self] = rh[self]
       THEN /\ mem' = [mem EXCEPT ![nd[self]].L = Dummy]
            /\ pc' = [pc EXCEPT ![self] = "PR5"]
       ELSE /\ mem' = [mem EXCEPT ![nd[self]].L = rh[self]]
            /\ pc' = [pc EXCEPT ![self] = "PR7"]
  /\ UNCHANGED << freeList, LeftHat, RightHat, valBag, locals >>

PR5(self) ==
  /\ pc[self] = "PR5"
  /\ lh' = [lh EXCEPT ![self] = LeftHat]
  /\ pc' = [pc EXCEPT ![self] = "PR6"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rh, rhR, rhL, lhL, lhR, retVal, pushVal >>

PR6(self) ==
  /\ pc[self] = "PR6"
  /\ IF RightHat = rh[self] /\ LeftHat = lh[self]
       THEN /\ RightHat' = nd[self]
            /\ LeftHat' = nd[self]
            /\ retVal' = [retVal EXCEPT ![self] = "okay"]
            /\ pc' = [pc EXCEPT ![self] = "T2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "PR2"]
            /\ UNCHANGED << RightHat, LeftHat, retVal >>
  /\ UNCHANGED << mem, freeList, valBag, nd, rh, rhR, rhL, lh, lhL, lhR, pushVal >>

PR7(self) ==
  /\ pc[self] = "PR7"
  /\ IF RightHat = rh[self] /\ mem[rh[self]].R = rhR[self]
       THEN /\ RightHat' = nd[self]
            /\ mem' = [mem EXCEPT ![rh[self]].R = nd[self]]
            /\ retVal' = [retVal EXCEPT ![self] = "okay"]
            /\ pc' = [pc EXCEPT ![self] = "T2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "PR2"]
            /\ UNCHANGED << RightHat, mem, retVal >>
  /\ UNCHANGED << freeList, LeftHat, valBag, nd, rh, rhR, rhL, lh, lhL, lhR, pushVal >>

(*************************** pushLeft ***************************************)
PL1(self) ==
  /\ pc[self] = "PL1"
  /\ IF freeList = {}
       THEN /\ retVal' = [retVal EXCEPT ![self] = "full"]
            /\ pc' = [pc EXCEPT ![self] = "T2"]
            /\ UNCHANGED << mem, freeList, nd >>
       ELSE \E a \in freeList :
              /\ nd' = [nd EXCEPT ![self] = a]
              /\ freeList' = freeList \ {a}
              /\ mem' = [mem EXCEPT ![a] = [L |-> Dummy, R |-> null,
                                            V |-> pushVal[self]]]
              /\ pc' = [pc EXCEPT ![self] = "PL2"]
              /\ UNCHANGED retVal
  /\ UNCHANGED << LeftHat, RightHat, valBag, rh, rhR, rhL, lh, lhL, lhR, pushVal >>

PL2(self) ==
  /\ pc[self] = "PL2"
  /\ lh' = [lh EXCEPT ![self] = LeftHat]
  /\ pc' = [pc EXCEPT ![self] = "PL3"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rh, rhR, rhL, lhL, lhR, retVal, pushVal >>

PL3(self) ==
  /\ pc[self] = "PL3"
  /\ lhL' = [lhL EXCEPT ![self] = mem[lh[self]].L]
  /\ pc' = [pc EXCEPT ![self] = "PL4"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rh, rhR, rhL, lh, lhR, retVal, pushVal >>

PL4(self) ==
  /\ pc[self] = "PL4"
  /\ IF lhL[self] = lh[self]
       THEN /\ mem' = [mem EXCEPT ![nd[self]].R = Dummy]
            /\ pc' = [pc EXCEPT ![self] = "PL5"]
       ELSE /\ mem' = [mem EXCEPT ![nd[self]].R = lh[self]]
            /\ pc' = [pc EXCEPT ![self] = "PL7"]
  /\ UNCHANGED << freeList, LeftHat, RightHat, valBag, locals >>

PL5(self) ==
  /\ pc[self] = "PL5"
  /\ rh' = [rh EXCEPT ![self] = RightHat]
  /\ pc' = [pc EXCEPT ![self] = "PL6"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rhR, rhL, lh, lhL, lhR, retVal, pushVal >>

PL6(self) ==
  /\ pc[self] = "PL6"
  /\ IF LeftHat = lh[self] /\ RightHat = rh[self]
       THEN /\ LeftHat' = nd[self]
            /\ RightHat' = nd[self]
            /\ retVal' = [retVal EXCEPT ![self] = "okay"]
            /\ pc' = [pc EXCEPT ![self] = "T2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "PL2"]
            /\ UNCHANGED << RightHat, LeftHat, retVal >>
  /\ UNCHANGED << mem, freeList, valBag, nd, rh, rhR, rhL, lh, lhL, lhR, pushVal >>

PL7(self) ==
  /\ pc[self] = "PL7"
  /\ IF LeftHat = lh[self] /\ mem[lh[self]].L = lhL[self]
       THEN /\ LeftHat' = nd[self]
            /\ mem' = [mem EXCEPT ![lh[self]].L = nd[self]]
            /\ retVal' = [retVal EXCEPT ![self] = "okay"]
            /\ pc' = [pc EXCEPT ![self] = "T2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "PL2"]
            /\ UNCHANGED << LeftHat, mem, retVal >>
  /\ UNCHANGED << freeList, RightHat, valBag, nd, rh, rhR, rhL, lh, lhL, lhR, pushVal >>

(*************************** popRight ***************************************)
OR1(self) ==
  /\ pc[self] = "OR1"
  /\ rh' = [rh EXCEPT ![self] = RightHat]
  /\ pc' = [pc EXCEPT ![self] = "OR2"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rhR, rhL, lh, lhL, lhR, retVal, pushVal >>

OR2(self) ==
  /\ pc[self] = "OR2"
  /\ lh' = [lh EXCEPT ![self] = LeftHat]
  /\ pc' = [pc EXCEPT ![self] = "OR3"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rh, rhR, rhL, lhL, lhR, retVal, pushVal >>

OR3(self) ==
  /\ pc[self] = "OR3"
  /\ rhR' = [rhR EXCEPT ![self] = mem[rh[self]].R]
  /\ pc' = [pc EXCEPT ![self] = "OR4"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rh, rhL, lh, lhL, lhR, retVal, pushVal >>

OR4(self) ==
  /\ pc[self] = "OR4"
  /\ IF rhR[self] = rh[self]
       THEN /\ retVal' = [retVal EXCEPT ![self] = "empty"]
            /\ pc' = [pc EXCEPT ![self] = "T3"]
       ELSE /\ IF rh[self] = lh[self]
                 THEN pc' = [pc EXCEPT ![self] = "OR5"]
                 ELSE pc' = [pc EXCEPT ![self] = "OR6"]
            /\ UNCHANGED retVal
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rh, rhR, rhL, lh, lhL, lhR, pushVal >>

OR5(self) ==
  /\ pc[self] = "OR5"
  /\ IF RightHat = rh[self] /\ LeftHat = lh[self]
       THEN /\ RightHat' = Dummy
            /\ LeftHat' = Dummy
            /\ pc' = [pc EXCEPT ![self] = "OR8"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "OR1"]
            /\ UNCHANGED << RightHat, LeftHat >>
  /\ UNCHANGED << mem, freeList, valBag, locals >>

OR6(self) ==
  /\ pc[self] = "OR6"
  /\ rhL' = [rhL EXCEPT ![self] = mem[rh[self]].L]
  /\ pc' = [pc EXCEPT ![self] = "OR7"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rh, rhR, lh, lhL, lhR, retVal, pushVal >>

OR7(self) ==
  /\ pc[self] = "OR7"
  /\ IF RightHat = rh[self] /\ mem[rh[self]].L = rhL[self]
       THEN /\ RightHat' = rhL[self]
            /\ mem' = [mem EXCEPT ![rh[self]].L = rh[self]]
            /\ pc' = [pc EXCEPT ![self] = "OR9"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "OR1"]
            /\ UNCHANGED << RightHat, mem >>
  /\ UNCHANGED << freeList, LeftHat, valBag, locals >>

OR8(self) ==
  /\ pc[self] = "OR8"
  /\ retVal' = [retVal EXCEPT ![self] = mem[rh[self]].V]
  /\ pc' = [pc EXCEPT ![self] = "T3"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rh, rhR, rhL, lh, lhL, lhR, pushVal >>

OR9(self) ==
  /\ pc[self] = "OR9"
  /\ retVal' = [retVal EXCEPT ![self] = mem[rh[self]].V]
  /\ pc' = [pc EXCEPT ![self] = "OR10"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rh, rhR, rhL, lh, lhL, lhR, pushVal >>

OR10(self) ==
  /\ pc[self] = "OR10"
  /\ mem' = [mem EXCEPT ![rh[self]].R = Dummy]
  /\ pc' = [pc EXCEPT ![self] = "T3"]
  /\ UNCHANGED << freeList, LeftHat, RightHat, valBag, locals >>

(*************************** popLeft ****************************************)
OL1(self) ==
  /\ pc[self] = "OL1"
  /\ lh' = [lh EXCEPT ![self] = LeftHat]
  /\ pc' = [pc EXCEPT ![self] = "OL2"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rh, rhR, rhL, lhL, lhR, retVal, pushVal >>

OL2(self) ==
  /\ pc[self] = "OL2"
  /\ rh' = [rh EXCEPT ![self] = RightHat]
  /\ pc' = [pc EXCEPT ![self] = "OL3"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rhR, rhL, lh, lhL, lhR, retVal, pushVal >>

OL3(self) ==
  /\ pc[self] = "OL3"
  /\ lhL' = [lhL EXCEPT ![self] = mem[lh[self]].L]
  /\ pc' = [pc EXCEPT ![self] = "OL4"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rh, rhR, rhL, lh, lhR, retVal, pushVal >>

OL4(self) ==
  /\ pc[self] = "OL4"
  /\ IF lhL[self] = lh[self]
       THEN /\ retVal' = [retVal EXCEPT ![self] = "empty"]
            /\ pc' = [pc EXCEPT ![self] = "T3"]
       ELSE /\ IF lh[self] = rh[self]
                 THEN pc' = [pc EXCEPT ![self] = "OL5"]
                 ELSE pc' = [pc EXCEPT ![self] = "OL6"]
            /\ UNCHANGED retVal
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rh, rhR, rhL, lh, lhL, lhR, pushVal >>

OL5(self) ==
  /\ pc[self] = "OL5"
  /\ IF LeftHat = lh[self] /\ RightHat = rh[self]
       THEN /\ LeftHat' = Dummy
            /\ RightHat' = Dummy
            /\ pc' = [pc EXCEPT ![self] = "OL8"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "OL1"]
            /\ UNCHANGED << RightHat, LeftHat >>
  /\ UNCHANGED << mem, freeList, valBag, locals >>

OL6(self) ==
  /\ pc[self] = "OL6"
  /\ lhR' = [lhR EXCEPT ![self] = mem[lh[self]].R]
  /\ pc' = [pc EXCEPT ![self] = "OL7"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rh, rhR, rhL, lh, lhL, retVal, pushVal >>

OL7(self) ==
  /\ pc[self] = "OL7"
  /\ IF LeftHat = lh[self] /\ mem[lh[self]].R = lhR[self]
       THEN /\ LeftHat' = lhR[self]
            /\ mem' = [mem EXCEPT ![lh[self]].R = lh[self]]
            /\ pc' = [pc EXCEPT ![self] = "OL9"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "OL1"]
            /\ UNCHANGED << LeftHat, mem >>
  /\ UNCHANGED << freeList, RightHat, valBag, locals >>

OL8(self) ==
  /\ pc[self] = "OL8"
  /\ retVal' = [retVal EXCEPT ![self] = mem[lh[self]].V]
  /\ pc' = [pc EXCEPT ![self] = "T3"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rh, rhR, rhL, lh, lhL, lhR, pushVal >>

OL9(self) ==
  /\ pc[self] = "OL9"
  /\ retVal' = [retVal EXCEPT ![self] = mem[lh[self]].V]
  /\ pc' = [pc EXCEPT ![self] = "OL10"]
  /\ UNCHANGED << mem, freeList, LeftHat, RightHat, valBag,
                  nd, rh, rhR, rhL, lh, lhL, lhR, pushVal >>

OL10(self) ==
  /\ pc[self] = "OL10"
  /\ mem' = [mem EXCEPT ![lh[self]].L = Dummy]
  /\ pc' = [pc EXCEPT ![self] = "T3"]
  /\ UNCHANGED << freeList, LeftHat, RightHat, valBag, locals >>

test(self) ==
  \/ T1(self) \/ T2(self) \/ T3(self)
  \/ PR1(self) \/ PR2(self) \/ PR3(self) \/ PR4(self)
  \/ PR5(self) \/ PR6(self) \/ PR7(self)
  \/ PL1(self) \/ PL2(self) \/ PL3(self) \/ PL4(self)
  \/ PL5(self) \/ PL6(self) \/ PL7(self)
  \/ OR1(self) \/ OR2(self) \/ OR3(self) \/ OR4(self) \/ OR5(self)
  \/ OR6(self) \/ OR7(self) \/ OR8(self) \/ OR9(self) \/ OR10(self)
  \/ OL1(self) \/ OL2(self) \/ OL3(self) \/ OL4(self) \/ OL5(self)
  \/ OL6(self) \/ OL7(self) \/ OL8(self) \/ OL9(self) \/ OL10(self)

(*************************** Garbage collection *****************************)
Roots ==
  ({LeftHat, RightHat} \cup
   {x \in Address :
      \E p \in Procs :
         /\ pc[p] # "T1"
         /\ x \in {nd[p], rh[p], rhR[p], rhL[p], lh[p], lhL[p], lhR[p]}})
  \cap Address

Succ(S) == S \cup (({mem[a].L : a \in S} \cup {mem[a].R : a \in S}) \cap Address)

RECURSIVE ReachFrom(_, _)
ReachFrom(S, n) == IF n = 0 THEN S ELSE ReachFrom(Succ(S), n - 1)

Reachable == ReachFrom(Roots, Cardinality(Address))

Collect ==
  /\ GC
  /\ \E a \in Address \ (freeList \cup {Dummy} \cup Reachable) :
        freeList' = freeList \cup {a}
  /\ UNCHANGED << mem, LeftHat, RightHat, valBag, pc, locals >>

Next == (\E self \in Procs : test(self)) \/ Collect

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(test(self))

(*************************** Properties *************************************)
TypeOK ==
  /\ mem \in [Address -> Node]
  /\ freeList \subseteq Address
  /\ LeftHat \in Address
  /\ RightHat \in Address
  /\ valBag \in [Val -> Nat]

Liveness == \A p \in Procs : []<>(pc[p] = "T1")

Symmetry == Permutations(Val)
=============================================================================