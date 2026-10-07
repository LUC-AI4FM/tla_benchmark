----------------------------- MODULE TwoProcLock -----------------------------

EXTENDS Naturals, TLC

CONSTANTS Proc
ASSUME Proc = {1, 2}

VARIABLES lock, pc

Labels == {"l0", "l1", "cs", "l2"}
CR == {"cs", "l2"}
Vars == <<lock, pc>>

TypeOK ==
  /\ lock \in {0, 1}
  /\ \A i \in Proc: pc[i] \in Labels

LockInv ==
  /\ \A i, j \in Proc: i # j => ~(pc[i] \in CR /\ pc[j] \in CR)
  /\ (\E i \in Proc: pc[i] \in CR) => lock = 0

Init ==
  /\ lock = 1
  /\ pc = [i \in Proc |-> "l0"]

L0(i) ==
  /\ i \in Proc
  /\ pc[i] = "l0"
  /\ pc' = [pc EXCEPT ![i] = "l1"]
  /\ UNCHANGED lock

L1(i) ==
  /\ i \in Proc
  /\ pc[i] = "l1"
  /\ lock = 1
  /\ lock' = 0
  /\ pc' = [pc EXCEPT ![i] = "cs"]

CS(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "l2"]
  /\ UNCHANGED lock

L2(i) ==
  /\ i \in Proc
  /\ pc[i] = "l2"
  /\ lock' = 1
  /\ pc' = [pc EXCEPT ![i] = "l0"]

ProcStep(i) == L0(i) \/ L1(i) \/ CS(i) \/ L2(i)

Next == \E i \in Proc: ProcStep(i)

Spec == Init /\ [] [Next]_Vars

(***************************************************************************)
(* TLAPS proofs: TypeOK is an invariant of Spec                            *)
(***************************************************************************)

THEOREM InitAndNextImpliesAlwaysTypeOK ==
  Init /\ [] [Next]_Vars => [] TypeOK
PROOF
  <1>1 Init => TypeOK
    BY DEF Init, TypeOK, Labels
  <1>2 TypeOK /\ [Next]_Vars => TypeOK'
    PROOF
      <2>1 CASE UNCHANGED Vars
        OBVIOUS
      <2>2 CASE Next
        PICK i \in Proc: ProcStep(i) BY DEF Next, ProcStep
        <3>1 CASE L0(i)
          OBVIOUS BY DEF L0, TypeOK, Labels
        <3>2 CASE L1(i)
          OBVIOUS BY DEF L1, TypeOK, Labels
        <3>3 CASE CS(i)
          OBVIOUS BY DEF CS, TypeOK, Labels
        <3>4 CASE L2(i)
          OBVIOUS BY DEF L2, TypeOK, Labels
        <3>5 QED
      <2>3 QED
  <1>3 QED BY <1>1, <1>2, PTL
QED

THEOREM SpecImpliesTypeOK ==
  Spec => [] TypeOK
PROOF
  BY InitAndNextImpliesAlwaysTypeOK, DEF Spec
QED

(***************************************************************************)
(* TLAPS proofs: LockInv (mutual exclusion) is an invariant of Spec        *)
(***************************************************************************)

LEMMA LockInvInit ==
  Init => LockInv
PROOF
  OBVIOUS BY DEF Init, LockInv, CR
QED

LEMMA LockInvPreservation ==
  LockInv /\ [Next]_Vars => LockInv'
PROOF
  <1>1 CASE UNCHANGED Vars
    OBVIOUS
  <1>2 CASE Next
    PICK i \in Proc: ProcStep(i) BY DEF Next, ProcStep
    <2>1 CASE L0(i)
      (*
        A move l0 -> l1 does not enter or leave CR and does not change lock.
      *)
      OBVIOUS BY DEF L0, LockInv, CR
    <2>2 CASE L1(i)
      (*
        Pre: lock = 1. From LockInv, (∃ j: pc[j] \in CR) => lock = 0,
        hence with lock = 1 we have no process in CR before the step.
        Post: i moves into "cs" and lock' = 0; others' pc unchanged.
        Thus at most i is in CR', and if someone is in CR' then lock' = 0.
      *)
      OBVIOUS BY DEF L1, LockInv, CR
    <2>3 CASE CS(i)
      (*
        A move cs -> l2 stays within CR and does not change lock,
        so exclusivity and implication are preserved.
      *)
      OBVIOUS BY DEF CS, LockInv, CR
    <2>4 CASE L2(i)
      (*
        A move l2 -> l0 leaves CR and sets lock' = 1.
        Since at most one process was in CR before (LockInv),
        after the step no process is in CR', so the implication is vacuously true.
      *)
      OBVIOUS BY DEF L2, LockInv, CR
    <2>5 QED
  <1>3 QED
QED

THEOREM InitAndNextImpliesAlwaysLockInv ==
  Init /\ [] [Next]_Vars => [] LockInv
PROOF
  <1>1 LockInvInit
  <1>2 LockInvPreservation
  <1>3 QED BY <1>1, <1>2, PTL
QED

THEOREM SpecImpliesLockInv ==
  Spec => [] LockInv
PROOF
  BY InitAndNextImpliesAlwaysLockInv, DEF Spec
QED

=============================================================================