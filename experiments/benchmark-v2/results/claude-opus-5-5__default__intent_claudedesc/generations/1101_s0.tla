------------------------------- MODULE Peterson -------------------------------
EXTENDS Naturals, TLAPS

\* Peterson's algorithm for two processes, with an inductive invariant,
\* mutual exclusion, and a refinement mapping to an abstract lock.
\* All three are proved with TLAPS.

Procs  == {0, 1}
Other(p) == 1 - p

Labels == {"ncs", "set_turn", "wait", "cs"}

VARIABLES flag, turn, pc

vars == <<flag, turn, pc>>

-----------------------------------------------------------------------------
\* Concrete protocol

Init == /\ flag = [i \in Procs |-> FALSE]
        /\ turn \in Procs
        /\ pc   = [i \in Procs |-> "ncs"]

\* Signal intent to enter
SetFlag(p) == /\ pc[p] = "ncs"
              /\ flag' = [flag EXCEPT ![p] = TRUE]
              /\ pc'   = [pc EXCEPT ![p] = "set_turn"]
              /\ UNCHANGED turn

\* Yield the turn to the other process
SetTurn(p) == /\ pc[p] = "set_turn"
              /\ turn' = Other(p)
              /\ pc'   = [pc EXCEPT ![p] = "wait"]
              /\ UNCHANGED flag

\* Wait until the other is not interested or it is our turn
Wait(p) == /\ pc[p] = "wait"
           /\ (flag[Other(p)] = FALSE \/ turn = p)
           /\ pc' = [pc EXCEPT ![p] = "cs"]
           /\ UNCHANGED <<flag, turn>>

\* Leave the critical section and retract intent
Exit(p) == /\ pc[p] = "cs"
           /\ flag' = [flag EXCEPT ![p] = FALSE]
           /\ pc'   = [pc EXCEPT ![p] = "ncs"]
           /\ UNCHANGED turn

Proc(p) == SetFlag(p) \/ SetTurn(p) \/ Wait(p) \/ Exit(p)

Next == \E p \in Procs : Proc(p)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Properties

TypeOK == /\ flag \in [Procs -> BOOLEAN]
          /\ turn \in Procs
          /\ pc   \in [Procs -> Labels]

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Each process's flag matches its program location
FlagInv == \A i \in Procs : flag[i] <=> (pc[i] \in {"set_turn", "wait", "cs"})

\* A process in the critical section holds the turn, or the other process
\* has not yet reached the point of yielding the turn
CSInv == \A i \in Procs :
            pc[i] = "cs" => (turn = i \/ pc[Other(i)] \in {"ncs", "set_turn"})

Inv == TypeOK /\ FlagInv /\ CSInv

-----------------------------------------------------------------------------
\* Abstract lock specification (parameterized by its state variable)

LockInit(lk) == lk = [i \in Procs |-> "idle"]

LockAcquire(lk, p) == /\ lk[p] = "idle"
                      /\ \A j \in Procs : lk[j] = "idle"
                      /\ lk' = [lk EXCEPT ![p] = "locked"]

LockRelease(lk, p) == /\ lk[p] = "locked"
                      /\ lk' = [lk EXCEPT ![p] = "idle"]

LockNext(lk) == \E p \in Procs : LockAcquire(lk, p) \/ LockRelease(lk, p)

LockSpec(lk) == LockInit(lk) /\ [][LockNext(lk)]_lk

LockMutex(lk) == \A i, j \in Procs : (i # j) => ~(lk[i] = "locked" /\ lk[j] = "locked")

\* Refinement mapping
absLock == [i \in Procs |-> IF pc[i] = "cs" THEN "locked" ELSE "idle"]

-----------------------------------------------------------------------------
\* Proofs

LEMMA OtherProps ==
    /\ \A p \in Procs : Other(p) \in Procs /\ Other(p) # p /\ Other(Other(p)) = p
    /\ \A p, r \in Procs : r # p => r = Other(p)
BY DEF Other, Procs

THEOREM InitInv == Init => Inv
BY DEF Init, Inv, TypeOK, FlagInv, CSInv, Procs, Labels

THEOREM NextInv == Inv /\ [Next]_vars => Inv'
<1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
  OBVIOUS
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars, Inv, TypeOK, FlagInv, CSInv
<1>2. ASSUME NEW p \in Procs, SetFlag(p) PROVE Inv'
  BY <1>2, OtherProps DEF SetFlag, Inv, TypeOK, FlagInv, CSInv, Labels
<1>3. ASSUME NEW p \in Procs, SetTurn(p) PROVE Inv'
  BY <1>3, OtherProps DEF SetTurn, Inv, TypeOK, FlagInv, CSInv, Labels
<1>4. ASSUME NEW p \in Procs, Wait(p) PROVE Inv'
  <2> DEFINE oth == Other(p)
  <2>1. oth \in Procs /\ oth # p /\ Other(oth) = p
    BY OtherProps
  <2>2. pc[oth] # "cs"
    BY <1>4, <2>1 DEF Wait, Inv, TypeOK, FlagInv, CSInv
  <2>3. turn = p \/ pc[oth] \in {"ncs", "set_turn"}
    BY <1>4, <2>1 DEF Wait, Inv, TypeOK, FlagInv, CSInv, Labels
  <2> QED
    BY <1>4, <2>1, <2>2, <2>3, OtherProps
       DEF Wait, Inv, TypeOK, FlagInv, CSInv, Labels
<1>5. ASSUME NEW p \in Procs, Exit(p) PROVE Inv'
  BY <1>5, OtherProps DEF Exit, Inv, TypeOK, FlagInv, CSInv, Labels
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next, Proc

THEOREM InvariantHolds == Spec => []Inv
BY InitInv, NextInv, PTL DEF Spec

THEOREM InvImpliesMutex == Inv => MutualExclusion
BY OtherProps DEF Inv, TypeOK, CSInv, MutualExclusion

THEOREM MutexHolds == Spec => []MutualExclusion
BY InvariantHolds, InvImpliesMutex, PTL

\* ---------------- Refinement of the abstract lock ----------------

LEMMA InitRefines == Init => LockInit(absLock)
BY DEF Init, LockInit, absLock

LEMMA StepRefines == Inv /\ [Next]_vars => [LockNext(absLock)]_absLock
<1> SUFFICES ASSUME Inv, [Next]_vars PROVE [LockNext(absLock)]_absLock
  OBVIOUS
<1>1. CASE UNCHANGED vars
  <2> absLock' = absLock
    BY <1>1 DEF vars, absLock
  <2> QED OBVIOUS
<1>2. ASSUME NEW p \in Procs, SetFlag(p) PROVE absLock' = absLock
  BY <1>2 DEF SetFlag, absLock, Inv, TypeOK
<1>3. ASSUME NEW p \in Procs, SetTurn(p) PROVE absLock' = absLock
  BY <1>3 DEF SetTurn, absLock, Inv, TypeOK
<1>4. ASSUME NEW p \in Procs, Wait(p) PROVE LockAcquire(absLock, p)
  <2> DEFINE oth == Other(p)
  <2>1. oth \in Procs /\ oth # p /\ Other(oth) = p
    BY OtherProps
  <2>2. pc[oth] # "cs"
    BY <1>4, <2>1 DEF Wait, Inv, TypeOK, FlagInv, CSInv
  <2>3. absLock[p] = "idle"
    BY <1>4 DEF Wait, absLock
  <2>4. \A j \in Procs : absLock[j] = "idle"
    BY <1>4, <2>1, <2>2, OtherProps DEF Wait, absLock
  <2>5. absLock' = [absLock EXCEPT ![p] = "locked"]
    BY <1>4 DEF Wait, absLock, Inv, TypeOK
  <2> QED
    BY <2>3, <2>4, <2>5 DEF LockAcquire
<1>5. ASSUME NEW p \in Procs, Exit(p) PROVE LockRelease(absLock, p)
  <2>1. absLock[p] = "locked"
    BY <1>5 DEF Exit, absLock
  <2>2. absLock' = [absLock EXCEPT ![p] = "idle"]
    BY <1>5 DEF Exit, absLock, Inv, TypeOK
  <2> QED
    BY <2>1, <2>2 DEF LockRelease
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next, Proc, LockNext

THEOREM Refinement == Spec => LockSpec(absLock)
<1>1. Init => LockInit(absLock)
  BY InitRefines
<1>2. Inv /\ [Next]_vars => [LockNext(absLock)]_absLock
  BY StepRefines
<1> QED
  BY <1>1, <1>2, InvariantHolds, PTL DEF Spec, LockSpec

=============================================================================