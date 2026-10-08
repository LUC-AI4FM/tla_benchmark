------------------------------ MODULE LockHS ------------------------------
EXTENDS Lock, Stuttering, P

VARIABLES s, h_turn

(* Variable tuple used in temporal operators *)
vars == <<pc, flag, turn, s, h_turn>>

InitHS ==
  /\ Lock.Init
  /\ h_turn = 1
  /\ s = top

l0HS ==
  /\ Lock.l0
  /\ UNCHANGED <<s, h_turn>>

csHS ==
  /\ Lock.cs
  /\ UNCHANGED <<s, h_turn>>

l2HS ==
  /\ Lock.l2
  /\ UNCHANGED <<s, h_turn>>

(* l1 wrapped with two stuttering steps *)
l1HS ==
  LET step == PostStutter(Lock.l1)
  IN
    /\ step
    /\ IF s' = bottom THEN h_turn' = pc[1] ELSE UNCHANGED h_turn

NextHS ==
  \/ l0HS
  \/ csHS
  \/ l2HS
  \/ l1HS

SpecHS == InitHS /\ [][NextHS]_vars

TypeOKHS ==
  /\ Lock.TypeOK
  /\ h_turn \in {1, 2}
  /\ s \in {top, bottom}

InvHS ==
  /\ (s = top => pc[1] # "cs" /\ pc[2] # "cs")
  /\ (s = bottom => pc[1] = "cs" \/ pc[2] = "cs")
  /\ h_turn = IF pc[1] = "cs" THEN 2 ELSE 1

LockInv == Lock.LockInv

Spec == Lock.Spec
PSpec == P.Spec
=============================================================================