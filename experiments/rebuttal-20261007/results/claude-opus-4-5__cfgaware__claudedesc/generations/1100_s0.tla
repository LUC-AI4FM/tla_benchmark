---------------------------- MODULE MutualExclusion ----------------------------
EXTENDS Integers, TLAPS

CONSTANTS Proc
ASSUME ProcAssumption == Proc = {1, 2}

VARIABLES lock, pc

vars == <<lock, pc>>

Labels == {"l0", "l1", "cs", "l2"}

TypeOK == 
    /\ lock \in {0, 1}
    /\ pc \in [Proc -> Labels]

Init == 
    /\ lock = 1
    /\ pc = [p \in Proc |-> "l0"]

(* Non-critical section - no-op, move to l1 *)
l0(p) == 
    /\ pc[p] = "l0"
    /\ pc' = [pc EXCEPT ![p] = "l1"]
    /\ lock' = lock

(* Acquire lock - wait until free, then take it *)
l1(p) == 
    /\ pc[p] = "l1"
    /\ lock = 1
    /\ lock' = 0
    /\ pc' = [pc EXCEPT ![p] = "cs"]

(* Critical section - no-op, move to l2 *)
cs(p) == 
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "l2"]
    /\ lock' = lock

(* Release lock *)
l2(p) == 
    /\ pc[p] = "l2"
    /\ lock' = 1
    /\ pc' = [pc EXCEPT ![p] = "l0"]

Next == \E p \in Proc : l0(p) \/ l1(p) \/ cs(p) \/ l2(p)

Spec == Init /\ [][Next]_vars

(* Mutual exclusion invariant *)
LockInv == 
    /\ \A p, q \in Proc : (p # q) => ~(pc[p] \in {"cs", "l2"} /\ pc[q] \in {"cs", "l2"})
    /\ \A p \in Proc : (pc[p] \in {"cs", "l2"}) => (lock = 0)

-----------------------------------------------------------------------------
(* TLAPS Proofs *)

THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY ProcAssumption DEF Init, TypeOK, Labels
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2>1. SUFFICES ASSUME TypeOK, Next PROVE TypeOK'
    BY DEF TypeOK, vars
  <2>2. PICK p \in Proc : l0(p) \/ l1(p) \/ cs(p) \/ l2(p)
    BY <2>1 DEF Next
  <2>3. CASE l0(p)
    BY <2>1, <2>3, ProcAssumption DEF l0, TypeOK, Labels
  <2>4. CASE l1(p)
    BY <2>1, <2>4, ProcAssumption DEF l1, TypeOK, Labels
  <2>5. CASE cs(p)
    BY <2>1, <2>5, ProcAssumption DEF cs, TypeOK, Labels
  <2>6. CASE l2(p)
    BY <2>1, <2>6, ProcAssumption DEF l2, TypeOK, Labels
  <2>7. QED
    BY <2>2, <2>3, <2>4, <2>5, <2>6
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM MutualExclusion == Spec => []LockInv
<1>1. Init => LockInv
  BY ProcAssumption DEF Init, LockInv
<1>2. TypeOK /\ LockInv /\ [Next]_vars => LockInv'
  <2>1. SUFFICES ASSUME TypeOK, LockInv, Next PROVE LockInv'
    BY DEF LockInv, vars
  <2>2. PICK p \in Proc : l0(p) \/ l1(p) \/ cs(p) \/ l2(p)
    BY <2>1 DEF Next
  <2>3. CASE l0(p)
    BY <2>1, <2>3, ProcAssumption DEF l0, LockInv, TypeOK, Labels
  <2>4. CASE l1(p)
    BY <2>1, <2>4, ProcAssumption DEF l1, LockInv, TypeOK, Labels
  <2>5. CASE cs(p)
    BY <2>1, <2>5, ProcAssumption DEF cs, LockInv, TypeOK, Labels
  <2>6. CASE l2(p)
    BY <2>1, <2>6, ProcAssumption DEF l2, LockInv, TypeOK, Labels
  <2>7. QED
    BY <2>2, <2>3, <2>4, <2>5, <2>6
<1>3. QED
  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

=============================================================================