------------------------------- MODULE LockProof -------------------------------
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

proc(self) == l0(self) \/ l1(self) \/ cs(self) \/ l2(self)

Next == \E self \in ProcSet : proc(self)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeOK == /\ lock \in {0, 1}
          /\ pc \in [ProcSet -> Labels]

LockInv ==
  /\ \A p, q \in ProcSet :
        p # q => ~(pc[p] \in {"cs", "l2"} /\ pc[q] \in {"cs", "l2"})
  /\ (\E p \in ProcSet : pc[p] \in {"cs", "l2"}) => lock = 0

-----------------------------------------------------------------------------

THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK, ProcSet, Labels
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK, [Next]_vars PROVE TypeOK'
    OBVIOUS
  <2>1. ASSUME NEW self \in ProcSet, l0(self) PROVE TypeOK'
    BY <2>1 DEF TypeOK, l0, Labels
  <2>2. ASSUME NEW self \in ProcSet, l1(self) PROVE TypeOK'
    BY <2>2 DEF TypeOK, l1, Labels
  <2>3. ASSUME NEW self \in ProcSet, cs(self) PROVE TypeOK'
    BY <2>3 DEF TypeOK, cs, Labels
  <2>4. ASSUME NEW self \in ProcSet, l2(self) PROVE TypeOK'
    BY <2>4 DEF TypeOK, l2, Labels
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF TypeOK, vars
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, proc
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM MutualExclusion == Spec => []LockInv
<1> DEFINE Inv == TypeOK /\ LockInv
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, LockInv, ProcSet, Labels
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2> USE DEF Inv, TypeOK, LockInv, ProcSet, Labels
  <2>1. ASSUME NEW self \in ProcSet, l0(self) PROVE Inv'
    BY <2>1 DEF l0
  <2>2. ASSUME NEW self \in ProcSet, l1(self) PROVE Inv'
    BY <2>2 DEF l1
  <2>3. ASSUME NEW self \in ProcSet, cs(self) PROVE Inv'
    BY <2>3 DEF cs
  <2>4. ASSUME NEW self \in ProcSet, l2(self) PROVE Inv'
    BY <2>4 DEF l2
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF vars
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, proc
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

=============================================================================