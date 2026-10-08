----------------------------- MODULE TwoProcLock -----------------------------

EXTENDS Naturals, TLC

CONSTANTS P1, P2
ASSUME P1 /= P2

(*
  Two-process mutual-exclusion lock with atomic acquire.
  Processes repeatedly go through locations:
    "NCS" (non-critical), "Acq" (acquire), "CS" (critical), "Rel" (release).
*)

Proc == {P1, P2}
Loc  == {"NCS", "Acq", "CS", "Rel"}

VARIABLES lock, pc

vars == << lock, pc >>

Hold(p) == pc[p] \in {"CS", "Rel"}
Holders == { p \in Proc : Hold(p) }

TypeOK ==
  /\ lock \in BOOLEAN
  /\ pc \in [Proc -> Loc]

Mutex ==
  \A p \in Proc : \A q \in Proc :
    p /= q => ~(Hold(p) /\ Hold(q))

LockReflects ==
  ( \E p \in Proc : Hold(p) ) => lock = TRUE

LockConsistency ==
  lock = TRUE <=> (\E p \in Proc : Hold(p))

Inv == /\ TypeOK
       /\ Mutex
       /\ LockConsistency

Init ==
  /\ lock = FALSE
  /\ pc = [p \in Proc |-> "NCS"]

NCSStep(p) ==
  /\ p \in Proc
  /\ pc[p] = "NCS"
  /\ pc' = [pc EXCEPT ![p] = "Acq"]
  /\ UNCHANGED lock

AcqStep(p) ==
  /\ p \in Proc
  /\ pc[p] = "Acq"
  /\ lock = FALSE
  /\ pc' = [pc EXCEPT ![p] = "CS"]
  /\ lock' = TRUE

CSStep(p) ==
  /\ p \in Proc
  /\ pc[p] = "CS"
  /\ pc' = [pc EXCEPT ![p] = "Rel"]
  /\ UNCHANGED lock

RelStep(p) ==
  /\ p \in Proc
  /\ pc[p] = "Rel"
  /\ pc' = [pc EXCEPT ![p] = "NCS"]
  /\ lock' = FALSE

Step(p) == NCSStep(p) \/ AcqStep(p) \/ CSStep(p) \/ RelStep(p)

Next == \E p \in Proc : Step(p)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(*                     TLAPS PROOFS OF INVARIANTS                          *)
(***************************************************************************)

THEOREM InitImpliesInv ==
  Init => Inv
PROOF
  OBVIOUS
  BY DEF Init, Inv, TypeOK, Mutex, LockConsistency, Hold, Proc, Loc
QED

LEMMA NCS_PreservesInv ==
  ASSUME Inv, NEW p \in Proc, NCSStep(p)
  PROVE Inv'
PROOF
  OBVIOUS
  BY DEF Inv, TypeOK, Mutex, LockConsistency, Hold, NCSStep
QED

LEMMA CS_PreservesInv ==
  ASSUME Inv, NEW p \in Proc, CSStep(p)
  PROVE Inv'
PROOF
  OBVIOUS
  BY DEF Inv, TypeOK, Mutex, LockConsistency, Hold, CSStep
QED

LEMMA Rel_PreservesInv ==
  ASSUME Inv, NEW p \in Proc, RelStep(p)
  PROVE Inv'
PROOF
  OBVIOUS
  BY DEF Inv, TypeOK, Mutex, LockConsistency, Hold, RelStep
QED

LEMMA Acq_PreservesInv ==
  ASSUME Inv, NEW p \in Proc, AcqStep(p)
  PROVE Inv'
PROOF
  OBVIOUS
  BY DEF Inv, TypeOK, Mutex, LockConsistency, Hold, AcqStep
QED

LEMMA StepPreservesInv ==
  ASSUME Inv, Next
  PROVE Inv'
PROOF
  SUFFICES ASSUME NEW p \in Proc, Step(p) PROVE Inv'
  PROOF
    CASE NCSStep(p)
      BY NCS_PreservesInv
    QED
    CASE AcqStep(p)
      BY Acq_PreservesInv
    QED
    CASE CSStep(p)
      BY CS_PreservesInv
    QED
    CASE RelStep(p)
      BY Rel_PreservesInv
    QED
  QED
  BY DEF Next, Step
QED

THEOREM InvIsInvariant ==
  Spec => []Inv
PROOF
  <1>1. Init => Inv BY InitImpliesInv
  <1>2. Inv /\ Next => Inv' BY StepPreservesInv
  <1>3. QED
    BY <1>1, <1>2, PTL DEF Spec, Next, Inv, vars
QED

(***************************************************************************)
(*        COROLLARY SAFETY PROPERTIES (AS REQUIRED IN THE TASK)            *)
(***************************************************************************)

THEOREM TypeCorrectnessAlways ==
  Spec => []TypeOK
PROOF
  SUFFICES ASSUME Spec PROVE []TypeOK
  PROOF
    HAVE []Inv BY InvIsInvariant
    OBVIOUS
    BY DEF Inv, TypeOK
  QED
QED

THEOREM MutualExclusionAndLockReflectionAlways ==
  Spec => []Mutex /\ [](LockReflects)
PROOF
  SUFFICES ASSUME Spec PROVE []Mutex /\ [](LockReflects)
  PROOF
    HAVE []Inv BY InvIsInvariant
    HAVE []Mutex BY DEF Inv, Mutex
    HAVE [](LockReflects) OBVIOUS BY DEF Inv, LockReflects, LockConsistency
    QED
  QED
QED

=============================================================================