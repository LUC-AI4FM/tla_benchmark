----------------------------- MODULE LockHS -----------------------------
EXTENDS Naturals, Lock, Stuttering

VARIABLES h_turn, s

HSVars == <<pc, c, h_turn, s>>

InitHS ==
  /\ Init
  /\ h_turn = 1
  /\ s = Top

TypeOKHS ==
  /\ TypeOK
  /\ h_turn \in Proc
  /\ s = Top \/ s \in [who: Proc, phase: {1, 2}]

IsActive(p, ph) == /\ s # Top
                   /\ s.who = p
                   /\ s.phase = ph

PostStutter1(p) ==
  /\ p \in Proc
  /\ pc[p] = "l1"
  /\ s = Top
  /\ s' = [who |-> p, phase |-> 1]
  /\ UNCHANGED <<pc, c, h_turn>>

PostStutter2(p) ==
  /\ p \in Proc
  /\ pc[p] = "l1"
  /\ IsActive(p, 1)
  /\ s' = [who |-> p, phase |-> 2]
  /\ h_turn' = Other(p)
  /\ UNCHANGED <<pc, c>>

DoL1(p) ==
  /\ p \in Proc
  /\ pc[p] = "l1"
  /\ IsActive(p, 2)
  /\ l1(p)
  /\ s' = Top
  /\ UNCHANGED h_turn

l1HS(p) == PostStutter1(p) \/ PostStutter2(p) \/ DoL1(p)

l0HS(p) ==
  /\ l0(p)
  /\ UNCHANGED <<h_turn, s>>

csHS(p) ==
  /\ cs(p)
  /\ UNCHANGED <<h_turn, s>>

l2HS(p) ==
  /\ l2(p)
  /\ UNCHANGED <<h_turn, s>>

NextHS == \E p \in Proc: l0HS(p) \/ l1HS(p) \/ csHS(p) \/ l2HS(p)

SpecHS == InitHS /\ [][NextHS]_HSVars

InvHS ==
  /\ TypeOKHS
  /\ (s # Top => pc[s.who] = "l1")
  /\ (s # Top /\ s.phase = 2 => h_turn = Other(s.who))
  /\ LockInv

pc_translation(pc_) == pc_
c_translation(c_) == c_

PSpec == P!SpecP(pc_translation(pc), h_turn)

LockSpec == Lock!Spec

THEOREM SpecHS => LockSpec
THEOREM SpecHS => PSpec
=============================================================================