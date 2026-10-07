```tla
MODULE LockHS

EXTENDS Lock, Stuttering

CONSTANTS P

VARIABLES h_turn, s, pc, c

InitHS == Init /\ h_turn = 1 /\ s = top

l0HS == l0 /\ h_turn' = h_turn

csHS == cs /\ h_turn' = h_turn

l1HS == IF s = top
        THEN PostStutter(l1, s, h_turn)
        ELSE l1 /\ h_turn' = h_turn

l2HS == l2 /\ h_turn' = h_turn

PostStutter(A, s, h_turn) ==
  IF s = top
  THEN A /\ s' = mid /\ h_turn' = IF pc[1] = "l1" THEN 2 ELSE 1
  ELSE A /\ s' = top /\ h_turn' = h_turn

TypeOKHS == TypeOK /\ (h_turn \in {1, 2}) /\ (s \in {top, mid})

InvHS == Inv /\ (s = top) => (pc[1] /= "l1" \/ h_turn = 1)
             /\ (s = mid) => (pc[1] = "l1" /\ h_turn = 2)

LockInv == LockTypeOK /\ []<>~(c[1] = c[2])

SpecHS == InitHS /\ [][NextHS]_<<pc, c, h_turn, s>>
           /\ WF_vars(NextHS)_{<<pc, c, h_turn, s>>}
           /\ InvHS
           /\ LockInv

PSpec == InitP /\ [][NextP]_vars
            /\ WF_vars(NextP)_vars
            /\ InvP

Spec == SpecHS /\ PSpec

NextHS == (l0HS \/ csHS \/ l1HS \/ l2HS)

THEOREM Spec => []LockInv
```