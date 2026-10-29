---------------------------- MODULE SimpleLock ----------------------------
EXTENDS Naturals, TLAPS

(***************************************************************************)
(* A mutual-exclusion lock shared by two processes.  Each process cycles   *)
(* through four control locations:                                         *)
(*   "ncs" : the non-critical section                                      *)
(*   "acq" : waiting to acquire the lock                                   *)
(*   "cs"  : the critical section                                          *)
(*   "rel" : the post-critical section, where the lock is released         *)
(* lock = 0 means the lock is free, lock = 1 means it is taken.            *)
(***************************************************************************)

Procs == {1, 2}

Locs == {"ncs", "acq", "cs", "rel"}

VARIABLES lock, pc

vars == << lock, pc >>

Init == /\ lock = 0
        /\ pc = [p \in Procs |-> "ncs"]

(* Leave the non-critical section and try to acquire the lock *)
NonCrit(self) == /\ pc[self] = "ncs"
                 /\ pc' = [pc EXCEPT ![self] = "acq"]
                 /\ UNCHANGED lock

(* Atomically wait until the lock is free and then take it *)
Acquire(self) == /\ pc[self] = "acq"
                 /\ lock = 0
                 /\ lock' = 1
                 /\ pc' = [pc EXCEPT ![self] = "cs"]

(* Execute the critical section *)
Crit(self) == /\ pc[self] = "cs"
              /\ pc' = [pc EXCEPT ![self] = "rel"]
              /\ UNCHANGED lock

(* Release the lock *)
Release(self) == /\ pc[self] = "rel"
                 /\ lock' = 0
                 /\ pc' = [pc EXCEPT ![self] = "ncs"]

Proc(self) == NonCrit(self) \/ Acquire(self) \/ Crit(self) \/ Release(self)

Next == \E self \in Procs : Proc(self)

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* Properties *)

TypeOK == /\ lock \in {0, 1}
          /\ pc \in [Procs -> Locs]

InCS(p) == pc[p] \in {"cs", "rel"}

MutualExclusion ==
    /\ \A i, j \in Procs : (i # j) => ~(InCS(i) /\ InCS(j))
    /\ \A i \in Procs : InCS(i) => lock = 1

Inv == TypeOK /\ MutualExclusion

---------------------------------------------------------------------------
(* Proofs *)

THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK, Locs
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK, [Next]_vars PROVE TypeOK'
    OBVIOUS
  <2>1. ASSUME NEW self \in Procs, NonCrit(self) PROVE TypeOK'
    BY <2>1 DEF TypeOK, NonCrit, Locs
  <2>2. ASSUME NEW self \in Procs, Acquire(self) PROVE TypeOK'
    BY <2>2 DEF TypeOK, Acquire, Locs
  <2>3. ASSUME NEW self \in Procs, Crit(self) PROVE TypeOK'
    BY <2>3 DEF TypeOK, Crit, Locs
  <2>4. ASSUME NEW self \in Procs, Release(self) PROVE TypeOK'
    BY <2>4 DEF TypeOK, Release, Locs
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF TypeOK, vars
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, Proc
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

LEMMA InitInv == Init => Inv
  BY DEF Init, Inv, TypeOK, MutualExclusion, InCS, Locs, Procs

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
<1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
  OBVIOUS
<1> USE DEF Inv, TypeOK, MutualExclusion, InCS, Locs
<1>1. ASSUME NEW self \in Procs, NonCrit(self) PROVE Inv'
  BY <1>1 DEF NonCrit
<1>2. ASSUME NEW self \in Procs, Acquire(self) PROVE Inv'
  BY <1>2 DEF Acquire
<1>3. ASSUME NEW self \in Procs, Crit(self) PROVE Inv'
  BY <1>3 DEF Crit
<1>4. ASSUME NEW self \in Procs, Release(self) PROVE Inv'
  BY <1>4 DEF Release
<1>5. CASE UNCHANGED vars
  BY <1>5 DEF vars
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next, Proc

THEOREM InvariantHolds == Spec => []Inv
  BY InitInv, NextInv, PTL DEF Spec

THEOREM MutexCorrect == Spec => []MutualExclusion
<1>1. Inv => MutualExclusion
  BY DEF Inv
<1> QED
  BY InvariantHolds, <1>1, PTL

=============================================================================