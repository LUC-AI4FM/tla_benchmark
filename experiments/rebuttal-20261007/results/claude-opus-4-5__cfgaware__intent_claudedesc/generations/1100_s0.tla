---------------------------- MODULE MutualExclusion ----------------------------
EXTENDS TLAPS

CONSTANTS Free, Held, NCS, Waiting, CS, PostCS

VARIABLES lock, pc

vars == <<lock, pc>>

Procs == {0, 1}

Init ==
    /\ lock = Free
    /\ pc = [p \in Procs |-> NCS]

\* Process p is in non-critical section and moves to waiting
EnterWaiting(p) ==
    /\ pc[p] = NCS
    /\ pc' = [pc EXCEPT ![p] = Waiting]
    /\ lock' = lock

\* Process p acquires the lock (atomically waits for free and takes it)
AcquireLock(p) ==
    /\ pc[p] = Waiting
    /\ lock = Free
    /\ lock' = Held
    /\ pc' = [pc EXCEPT ![p] = CS]

\* Process p finishes critical section and moves to post-critical section
ExitCS(p) ==
    /\ pc[p] = CS
    /\ pc' = [pc EXCEPT ![p] = PostCS]
    /\ lock' = lock

\* Process p releases the lock and returns to non-critical section
ReleaseLock(p) ==
    /\ pc[p] = PostCS
    /\ lock' = Free
    /\ pc' = [pc EXCEPT ![p] = NCS]

Next ==
    \E p \in Procs :
        \/ EnterWaiting(p)
        \/ AcquireLock(p)
        \/ ExitCS(p)
        \/ ReleaseLock(p)

Spec == Init /\ [][Next]_vars

\* Type correctness invariant
TypeOK ==
    /\ lock \in {Free, Held}
    /\ pc \in [Procs -> {NCS, Waiting, CS, PostCS}]

\* Mutual exclusion invariant
MutualExclusion ==
    ~(pc[0] \in {CS, PostCS} /\ pc[1] \in {CS, PostCS})

\* Lock consistency: if any process is in CS or PostCS, lock must be Held
LockConsistency ==
    \A p \in Procs : pc[p] \in {CS, PostCS} => lock = Held

\* Combined lock invariant
LockInv ==
    /\ MutualExclusion
    /\ LockConsistency

\* Inductive invariant combining TypeOK and LockInv
Inv == TypeOK /\ LockInv

--------------------------------------------------------------------------------
\* TLAPS Proofs
--------------------------------------------------------------------------------

THEOREM TypeCorrectness == Spec => []TypeOK
<1>1. Init => TypeOK
    BY DEF Init, TypeOK, Procs
<1>2. TypeOK /\ [Next]_vars => TypeOK'
    <2>1. ASSUME TypeOK, Next
          PROVE TypeOK'
        <3>1. ASSUME NEW p \in Procs, EnterWaiting(p)
              PROVE TypeOK'
            BY <3>1 DEF TypeOK, EnterWaiting, Procs
        <3>2. ASSUME NEW p \in Procs, AcquireLock(p)
              PROVE TypeOK'
            BY <3>2 DEF TypeOK, AcquireLock, Procs
        <3>3. ASSUME NEW p \in Procs, ExitCS(p)
              PROVE TypeOK'
            BY <3>3 DEF TypeOK, ExitCS, Procs
        <3>4. ASSUME NEW p \in Procs, ReleaseLock(p)
              PROVE TypeOK'
            BY <3>4 DEF TypeOK, ReleaseLock, Procs
        <3>5. QED
            BY <2>1, <3>1, <3>2, <3>3, <3>4 DEF Next
    <2>2. ASSUME TypeOK, UNCHANGED vars
          PROVE TypeOK'
        BY <2>2 DEF TypeOK, vars
    <2>3. QED
        BY <2>1, <2>2
<1>3. QED
    BY <1>1, <1>2, PTL DEF Spec

THEOREM MutualExclusionCorrectness == Spec => []LockInv
<1>1. Init => Inv
    BY DEF Init, Inv, TypeOK, LockInv, MutualExclusion, LockConsistency, Procs
<1>2. Inv /\ [Next]_vars => Inv'
    <2>1. ASSUME Inv, Next
          PROVE Inv'
        <3>1. ASSUME NEW p \in Procs, EnterWaiting(p)
              PROVE Inv'
            BY <3>1 DEF Inv, TypeOK, LockInv, MutualExclusion, LockConsistency, 
                        EnterWaiting, Procs
        <3>2. ASSUME NEW p \in Procs, AcquireLock(p)
              PROVE Inv'
            <4>1. TypeOK'
                BY <3>2 DEF Inv, TypeOK, AcquireLock, Procs
            <4>2. MutualExclusion'
                BY <3>2 DEF Inv, TypeOK, LockInv, MutualExclusion, LockConsistency,
                            AcquireLock, Procs
            <4>3. LockConsistency'
                BY <3>2 DEF Inv, TypeOK, LockInv, LockConsistency, AcquireLock, Procs
            <4>4. QED
                BY <4>1, <4>2, <4>3 DEF Inv, LockInv
        <3>3. ASSUME NEW p \in Procs, ExitCS(p)
              PROVE Inv'
            BY <3>3 DEF Inv, TypeOK, LockInv, MutualExclusion, LockConsistency, 
                        ExitCS, Procs
        <3>4. ASSUME NEW p \in Procs, ReleaseLock(p)
              PROVE Inv'
            <4>1. TypeOK'
                BY <3>4 DEF Inv, TypeOK, ReleaseLock, Procs
            <4>2. MutualExclusion'
                BY <3>4 DEF Inv, TypeOK, LockInv, MutualExclusion, LockConsistency,
                            ReleaseLock, Procs
            <4>3. LockConsistency'
                BY <3>4 DEF Inv, TypeOK, LockInv, MutualExclusion, LockConsistency, 
                            ReleaseLock, Procs
            <4>4. QED
                BY <4>1, <4>2, <4>3 DEF Inv, LockInv
        <3>5. QED
            BY <2>1, <3>1, <3>2, <3>3, <3>4 DEF Next
    <2>2. ASSUME Inv, UNCHANGED vars
          PROVE Inv'
        BY <2>2 DEF Inv, TypeOK, LockInv, MutualExclusion, LockConsistency, vars
    <2>3. QED
        BY <2>1, <2>2
<1>3. Inv => LockInv
    BY DEF Inv, LockInv
<1>4. QED
    BY <1>1, <1>2, <1>3, PTL DEF Spec

================================================================================