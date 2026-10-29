---------------------------- MODULE LockMutex ----------------------------
EXTENDS Naturals, TLAPS

VARIABLES lock, pc

vars == <<lock, pc>>

Procs == {0, 1}

Locs == {"ncs", "acq", "cs", "rel"}

(* lock = 1 means the lock is free, lock = 0 means it is held *)

Init == /\ lock = 1
        /\ pc = [p \in Procs |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "acq"]
             /\ UNCHANGED lock

acq(self) == /\ pc[self] = "acq"
             /\ lock = 1
             /\ lock' = 0
             /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "rel"]
            /\ UNCHANGED lock

rel(self) == /\ pc[self] = "rel"
             /\ lock' = 1
             /\ pc' = [pc EXCEPT ![self] = "ncs"]

proc(self) == ncs(self) \/ acq(self) \/ cs(self) \/ rel(self)

Next == \E self \in Procs : proc(self)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeOK == /\ lock \in {0, 1}
          /\ pc \in [Procs -> Locs]

LockInv == /\ \A p, q \in Procs :
                 (p # q) => ~(pc[p] \in {"cs", "rel"} /\ pc[q] \in {"cs", "rel"})
           /\ \A p \in Procs : pc[p] \in {"cs", "rel"} => lock = 0

Inv == TypeOK /\ LockInv

-----------------------------------------------------------------------------

THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK, Procs, Locs
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK, [Next]_vars PROVE TypeOK'
    OBVIOUS
  <2>1. ASSUME NEW self \in Procs, ncs(self) PROVE TypeOK'
    BY <2>1 DEF ncs, TypeOK, Locs
  <2>2. ASSUME NEW self \in Procs, acq(self) PROVE TypeOK'
    BY <2>2 DEF acq, TypeOK, Locs
  <2>3. ASSUME NEW self \in Procs, cs(self) PROVE TypeOK'
    BY <2>3 DEF cs, TypeOK, Locs
  <2>4. ASSUME NEW self \in Procs, rel(self) PROVE TypeOK'
    BY <2>4 DEF rel, TypeOK, Locs
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF vars, TypeOK
  <2>6. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, proc
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM MutualExclusion == Spec => []LockInv
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, LockInv, Procs, Locs
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2> USE DEF Inv, TypeOK, LockInv, Locs
  <2>1. ASSUME NEW self \in Procs, ncs(self) PROVE Inv'
    BY <2>1 DEF ncs
  <2>2. ASSUME NEW self \in Procs, acq(self) PROVE Inv'
    BY <2>2 DEF acq
  <2>3. ASSUME NEW self \in Procs, cs(self) PROVE Inv'
    BY <2>3 DEF cs
  <2>4. ASSUME NEW self \in Procs, rel(self) PROVE Inv'
    BY <2>4 DEF rel
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF vars
  <2>6. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, proc
<1>3. Inv => LockInv
  BY DEF Inv
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================