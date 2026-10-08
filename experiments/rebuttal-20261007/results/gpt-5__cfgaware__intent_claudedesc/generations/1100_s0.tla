------------------------------- MODULE TwoProcLock -------------------------------

EXTENDS TLC

CONSTANTS

VARIABLES lock, pc

Proc == {1, 2}

Loc == {"NCS", "Acq", "CS", "Post"}

Holds(p) == pc[p] \in {"CS", "Post"}

vars == << lock, pc >>

Init ==
  /\ lock = "Free"
  /\ pc = [p \in Proc |-> "NCS"]

NCS(p) ==
  /\ p \in Proc
  /\ pc[p] = "NCS"
  /\ pc' = [pc EXCEPT ![p] = "Acq"]
  /\ UNCHANGED lock

Acquire(p) ==
  /\ p \in Proc
  /\ pc[p] = "Acq"
  /\ lock = "Free"
  /\ lock' = "Taken"
  /\ pc' = [pc EXCEPT ![p] = "CS"]

CS(p) ==
  /\ p \in Proc
  /\ pc[p] = "CS"
  /\ pc' = [pc EXCEPT ![p] = "Post"]
  /\ UNCHANGED lock

Release(p) ==
  /\ p \in Proc
  /\ pc[p] = "Post"
  /\ lock' = "Free"
  /\ pc' = [pc EXCEPT ![p] = "NCS"]

Step(p) == NCS(p) \/ Acquire(p) \/ CS(p) \/ Release(p)

Next == \E p \in Proc : Step(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ lock \in {"Free", "Taken"}
  /\ \A p \in Proc : pc[p] \in Loc

MutEx ==
  \A p, q \in Proc : p # q => ~(Holds(p) /\ Holds(q))

LockReflect ==
  \A p \in Proc : Holds(p) => lock = "Taken"

LockInv == MutEx /\ LockReflect

THEOREM TypeOKInit == Init => TypeOK
PROOF
  OBVIOUS
QED

LEMMA TypeOKPreserved ==
  TypeOK /\ [Next]_vars => TypeOK'
PROOF
  SUFFICES ASSUME TypeOK, Next PROVE TypeOK'
  PROOF
    PICK p \in Proc : Step(p) BY DEF Next
    SUFFICES ASSUME NCS(p) PROVE TypeOK' 
    PROOF
      /\ CASE NCS(p)
      /\ OBVIOUS
    QED
    SUFFICES ASSUME Acquire(p) PROVE TypeOK'
    PROOF
      /\ CASE Acquire(p)
      /\ OBVIOUS
    QED
    SUFFICES ASSUME CS(p) PROVE TypeOK'
    PROOF
      /\ CASE CS(p)
      /\ OBVIOUS
    QED
    SUFFICES ASSUME Release(p) PROVE TypeOK'
    PROOF
      /\ CASE Release(p)
      /\ OBVIOUS
    QED
    OBVIOUS
  QED
  \* Stuttering case
  OBVIOUS
QED

THEOREM TypeOKInv == Spec => []TypeOK
PROOF
  <1>1 Init => TypeOK BY TypeOKInit
  <1>2 TypeOK /\ [Next]_vars => TypeOK' BY TypeOKPreserved
  <1>3 QED BY <1>1, <1>2, PTL DEF Spec
QED

LEMMA LockInvInit == Init => LockInv
PROOF
  OBVIOUS
QED

LEMMA LockInvPreserved ==
  LockInv /\ [Next]_vars => LockInv'
PROOF
  SUFFICES ASSUME LockInv, Next PROVE LockInv'
  PROOF
    PICK p \in Proc : Step(p) BY DEF Next
    \* Case 1: NCS step
    SUFFICES ASSUME NCS(p) PROVE LockInv'
    PROOF
      ASSUME Hncs == NCS(p)
      \* Only pc[p] changes to "Acq"; lock unchanged.
      \* Mutual exclusion preserved: no new holder is introduced, and none removed except possibly p (which is not a holder after NCS).
      <2>1 MutEx' BY Hncs, MutEx, DEF MutEx, Holds, NCS
      \* Lock reflection preserved: holders unchanged; lock unchanged.
      <2>2 LockReflect' BY Hncs, LockReflect, DEF LockReflect, Holds, NCS
      <2>3 QED BY <2>1, <2>2 DEF LockInv
    QED
    \* Case 2: Acquire step
    SUFFICES ASSUME Acquire(p) PROVE LockInv'
    PROOF
      ASSUME Hacq == Acquire(p)
      \* From LockInv and lock = "Free" before, no process holds before (by contrapositive of LockReflect).
      <2>1 \A q \in Proc : ~Holds(q)
        PROOF
          TAKE q \in Proc
          HAVE lock = "Free" BY Hacq, DEF Acquire
          HAVE Holds(q) => lock = "Taken" BY LockReflect, DEF LockReflect
          THUS ~Holds(q) BY CONTRADICTION
        QED
      \* After acquire, only p becomes a holder; others unchanged.
      <2>2 MutEx'
        PROOF
          \* If two distinct processes were holders after, one must be p and another q#p, but <2>1 shows no q held before and q is unchanged, contradiction.
          OBVIOUS
        QED
      \* Lock reflects holder after acquire: p holds and lock' = "Taken"; others do not hold.
      <2>3 LockReflect' BY Hacq, <2>1, DEF LockReflect, Holds, Acquire
      <2>4 QED BY <2>2, <2>3 DEF LockInv
    QED
    \* Case 3: CS step
    SUFFICES ASSUME CS(p) PROVE LockInv'
    PROOF
      ASSUME Hcs == CS(p)
      \* Only pc[p] moves CS->Post; holder set unchanged; lock unchanged.
      <2>1 MutEx' BY Hcs, MutEx, DEF MutEx, Holds, CS
      <2>2 LockReflect' BY Hcs, LockReflect, DEF LockReflect, Holds, CS
      <2>3 QED BY <2>1, <2>2 DEF LockInv
    QED
    \* Case 4: Release step
    SUFFICES ASSUME Release(p) PROVE LockInv'
    PROOF
      ASSUME Hrel == Release(p)
      \* p ceases to hold; lock becomes Free. No other process could have held before, otherwise two would have held (p in Post and that process), contradicting MutEx.
      <2>1 \A q \in Proc : q # p => ~Holds(q)
        PROOF
          TAKE q \in Proc
          ASSUME q # p
          HAVE Holds(p) BY Hrel, DEF Holds, Release
          HAVE ~(Holds(p) /\ Holds(q)) BY MutEx, `q # p`, DEF MutEx
          THUS ~Holds(q) OBVIOUS
        QED
      <2>2 MutEx' OBVIOUS
      <2>3 LockReflect'
        PROOF
          \* After release, no one holds; hence vacuously true. Also lock' = "Free".
          OBVIOUS
        QED
      <2>4 QED BY <2>2, <2>3 DEF LockInv
    QED
    OBVIOUS
  QED
  \* Stuttering case
  OBVIOUS
QED

THEOREM LockInvInv == Spec => []LockInv
PROOF
  <1>1 Init => LockInv BY LockInvInit
  <1>2 LockInv /\ [Next]_vars => LockInv' BY LockInvPreserved
  <1>3 QED BY <1>1, <1>2, PTL DEF Spec
QED

=============================================================================