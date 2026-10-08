------------------------------- MODULE TwoProcLock -------------------------------

EXTENDS Naturals, TLC

(*
  Two-process abstract mutual-exclusion lock with TLAPS proofs.
  Variables:
    - lock : integer in {0,1}, where 1 means "free" and 0 means "held"
    - pc   : program counter function from Proc to Labels
*)

CONSTANTS

VARIABLES lock, pc

Proc == {1, 2}

l0 == "l0"
l1 == "l1"
cs == "cs"
l2 == "l2"

Labels == {l0, l1, cs, l2}
Region == {cs, l2}

TypeOK ==
  /\ lock \in {0, 1}
  /\ pc \in [Proc -> Labels]

LockInv ==
  /\ \A p, q \in Proc: p # q => ~(pc[p] \in Region /\ pc[q] \in Region)
  /\ (\E p \in Proc: pc[p] \in Region) => lock = 0

Init ==
  /\ lock = 1
  /\ pc = [i \in Proc |-> l0]

L0(i) ==
  /\ i \in Proc
  /\ pc[i] = l0
  /\ pc' = [pc EXCEPT ![i] = l1]
  /\ UNCHANGED lock

L1(i) ==
  /\ i \in Proc
  /\ pc[i] = l1
  /\ lock = 1
  /\ lock' = 0
  /\ pc' = [pc EXCEPT ![i] = cs]

CS(i) ==
  /\ i \in Proc
  /\ pc[i] = cs
  /\ pc' = [pc EXCEPT ![i] = l2]
  /\ UNCHANGED lock

L2(i) ==
  /\ i \in Proc
  /\ pc[i] = l2
  /\ lock' = 1
  /\ pc' = [pc EXCEPT ![i] = l0]

Next ==
  \E i \in Proc: L0(i) \/ L1(i) \/ CS(i) \/ L2(i)

vars == << lock, pc >>

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* TLAPS proofs                                                            *)
(***************************************************************************)

THEOREM SpecImpliesTypeOK ==
  Spec => []TypeOK
PROOF
  SUFFICES ASSUME Init, Next PROVE []TypeOK BY DEF Spec
  <2>1. Init => TypeOK
    BY DEF Init, TypeOK, Proc, Labels, l0
  <2>2. ASSUME TypeOK, [Next]_vars PROVE TypeOK'
  PROOF
    CASE Next
    <3>1. PICK i \in Proc SUCH THAT L0(i) \/ L1(i) \/ CS(i) \/ L2(i)
      PROOF
        SUFFICES ASSUME i \in Proc PROVE
                 (L0(i) => TypeOK') /\ (L1(i) => TypeOK') /\ (CS(i) => TypeOK') /\ (L2(i) => TypeOK')
        PROOF
          <5>1. L0(i) => TypeOK'
            BY DEF L0, TypeOK, Labels
          <5>2. L1(i) => TypeOK'
            BY DEF L1, TypeOK, Labels
          <5>3. CS(i) => TypeOK'
            BY DEF CS, TypeOK, Labels
          <5>4. L2(i) => TypeOK'
            BY DEF L2, TypeOK, Labels
          <5>5. QED BY <5>1, <5>2, <5>3, <5>4
        QED
      QED
    CASE UNCHANGED vars
    <3>2. TypeOK'               (*
                                  Stuttering preserves TypeOK since lock' = lock and pc' = pc
                                *)
      BY DEF TypeOK, vars
  QED
  <2>3. QED BY <2>1, <2>2, PTL
QED

THEOREM SpecImpliesLockInv ==
  Spec => []LockInv
PROOF
  SUFFICES ASSUME Init, Next PROVE []LockInv BY DEF Spec
  <2>1. Init => LockInv
    PROOF
      <3>1. \A p, q \in Proc: p # q => ~(pc[p] \in Region /\ pc[q] \in Region)
        BY DEF Init, Region
      <3>2. ((\E p \in Proc: pc[p] \in Region) => lock = 0)
        BY DEF Init, Region
      <3>3. QED BY <3>1, <3>2, DEF LockInv
    QED
  <2>2. ASSUME LockInv, [Next]_vars PROVE LockInv'
  PROOF
    CASE Next
    <3>1. PICK i \in Proc SUCH THAT L0(i) \/ L1(i) \/ CS(i) \/ L2(i)
      PROOF
        SUFFICES ASSUME i \in Proc PROVE
                 (L0(i) => LockInv') /\ (L1(i) => LockInv') /\ (CS(i) => LockInv') /\ (L2(i) => LockInv')
        PROOF
          <5>1. L0(i) => LockInv'
            (*
              L0 does not change lock and moves pc[i] from l0 to l1 (both not in Region),
              so both conjuncts of LockInv are preserved.
            *)
            BY DEF L0, LockInv, Region
          <5>2. L1(i) => LockInv'
            (*
              Entering cs requires lock = 1 and sets lock' = 0 while moving pc[i] to cs.
              - Mutual exclusion: If some j != i were already in Region, then by LockInv we would have lock = 0,
                contradicting the guard lock = 1 of L1(i). Hence no other process is in Region, and after the step
                at most i is in Region.
              - Lock condition: Since L1 sets lock' = 0 and places i in Region, the implication holds in the next state.
            *)
            BY DEF L1, LockInv, Region, Proc
          <5>3. CS(i) => LockInv'
            (*
              CS moves within Region and does not change lock. Pre-state LockInv implies lock = 0 when in Region;
              thus lock remains 0, and mutual exclusion is preserved.
            *)
            BY DEF CS, LockInv, Region
          <5>4. L2(i) => LockInv'
            (*
              L2 releases: it sets lock' = 1 and moves pc[i] from l2 to l0 (leaving Region).
              - Mutual exclusion: Either Region was empty or contained only i; after the step, i leaves Region, so no pair exists.
              - Lock condition: If some process is in Region after the step, it must be a process different from i.
                But since only i moved and others' pcs are unchanged, no other process can newly be in Region.
                Hence the antecedent of the implication is false, and the condition holds trivially.
            *)
            BY DEF L2, LockInv, Region
          <5>5. QED BY <5>1, <5>2, <5>3, <5>4
        QED
      QED
    CASE UNCHANGED vars
    <3>2. LockInv'               (*
                                   Stuttering preserves LockInv since lock' = lock and pc' = pc
                                 *)
      BY DEF LockInv, vars
  QED
  <2>3. QED BY <2>1, <2>2, PTL
QED

=============================================================================