---------------------------- MODULE LockProof ----------------------------
(***************************************************************************)
(* An abstract mutual-exclusion lock shared by two processes, together     *)
(* with TLAPS proofs of type correctness and mutual exclusion.             *)
(*                                                                         *)
(* Each process runs an infinite loop:                                     *)
(*   l0: non-critical section (no-op)                                      *)
(*   l1: await lock = 1; lock := 0                                         *)
(*   cs: critical section (no-op)                                          *)
(*   l2: lock := 1                                                         *)
(***************************************************************************)
EXTENDS Integers, TLAPS

VARIABLES lock, pc

vars == << lock, pc >>

ProcSet == {1, 2}

Labels == {"l0", "l1", "cs", "l2"}

Init == /\ lock = 1
        /\ pc = [self \in ProcSet |-> "l0"]

l0(self) == /\ pc[self] = "l0"
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ UNCHANGED lock

l1(self) == /\ pc[self] = "l1"
            /\ lock = 1
            /\ lock' = 0
            /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED lock

l2(self) == /\ pc[self] = "l2"
            /\ lock' = 1
            /\ pc' = [pc EXCEPT ![self] = "l0"]

P(self) == l0(self) \/ l1(self) \/ cs(self) \/ l2(self)

Next == \E self \in ProcSet : P(self)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeOK == /\ lock \in {0, 1}
          /\ pc \in [ProcSet -> Labels]

InCS(i) == pc[i] \in {"cs", "l2"}

LockInv == /\ \A i, j \in ProcSet : (i # j) => ~(InCS(i) /\ InCS(j))
           /\ (\E i \in ProcSet : InCS(i)) => lock = 0

Inv == TypeOK /\ LockInv

-----------------------------------------------------------------------------
(***************************************************************************)
(* Proofs                                                                  *)
(***************************************************************************)

THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK, ProcSet, Labels
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK, [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <2>1. ASSUME NEW self \in ProcSet, l0(self)
        PROVE  TypeOK'
    BY <2>1 DEF TypeOK, l0, Labels
  <2>2. ASSUME NEW self \in ProcSet, l1(self)
        PROVE  TypeOK'
    BY <2>2 DEF TypeOK, l1, Labels
  <2>3. ASSUME NEW self \in ProcSet, cs(self)
        PROVE  TypeOK'
    BY <2>3 DEF TypeOK, cs, Labels
  <2>4. ASSUME NEW self \in ProcSet, l2(self)
        PROVE  TypeOK'
    BY <2>4 DEF TypeOK, l2, Labels
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF TypeOK, vars
  <2>6. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, P
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM MutualExclusion == Spec => []LockInv
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, LockInv, InCS, ProcSet, Labels
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. ASSUME NEW self \in ProcSet, l0(self)
        PROVE  Inv'
    BY <2>1 DEF Inv, TypeOK, LockInv, InCS, l0, Labels, ProcSet
  <2>2. ASSUME NEW self \in ProcSet, l1(self)
        PROVE  Inv'
    <3>1. \A i \in ProcSet : ~InCS(i)
      BY <2>2 DEF Inv, LockInv, l1
    <3>2. TypeOK'
      BY <2>2 DEF Inv, TypeOK, l1, Labels
    <3>3. LockInv'
      BY <2>2, <3>1 DEF Inv, TypeOK, LockInv, InCS, l1, ProcSet
    <3>4. QED
      BY <3>2, <3>3 DEF Inv
  <2>3. ASSUME NEW self \in ProcSet, cs(self)
        PROVE  Inv'
    BY <2>3 DEF Inv, TypeOK, LockInv, InCS, cs, Labels, ProcSet
  <2>4. ASSUME NEW self \in ProcSet, l2(self)
        PROVE  Inv'
    <3>1. \A i \in ProcSet : i # self => ~InCS(i)
      BY <2>4 DEF Inv, LockInv, InCS, l2
    <3>2. TypeOK'
      BY <2>4 DEF Inv, TypeOK, l2, Labels
    <3>3. LockInv'
      BY <2>4, <3>1 DEF Inv, TypeOK, LockInv, InCS, l2, ProcSet
    <3>4. QED
      BY <3>2, <3>3 DEF Inv
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF Inv, TypeOK, LockInv, InCS, vars
  <2>6. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, P
<1>3. Inv => LockInv
  BY DEF Inv
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================