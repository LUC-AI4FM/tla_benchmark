--------------------------- MODULE LockHS ---------------------------
EXTENDS Lock, Stuttering, Peterson

VARIABLES h_turn, s, pc, c

InitHS == Init /\ h_turn = 1 /\ s = top
l1HS(p) == /\ l1(p)
           /\ PostStutter(s, pc, "l1", p)
           /\ IF s' = "l1" THEN h_turn' = p ELSE h_turn' = h_turn
           /\ UNCHANGED <<c, pc>>
l0(p) == l0(p) /\ UNCHANGED <<h_turn, s>>
cs(p) == cs(p) /\ UNCHANGED <<h_turn, s>>
l2(p) == l2(p) /\ UNCHANGED <<h_turn, s>>

TypeOKHS == /\ pc \in [1..3]
            /\ c \in {0, 1}
            /\ h_turn \in {1, 2}
            /\ s \in {"top", "l1", "l2"}
InvHS == /\ (s = "top") => (h_turn = 1 \/ h_turn = 2)
         /\ (s = "l1") => (pc[1] = 2)
         /\ (s = "l2") => (pc[2] = 2)
LockInv == LockInv

SpecHS == /\ InitHS
          /\ [][NextHS]_<<h_turn, s, pc, c>>
TypeOK == TypeOKHS
NextHS == \/ \E p \in {1, 2} : l0(p)
           \/ \E p \in {1, 2} : l1HS(p)
           \/ \E p \in {1, 2} : cs(p)
           \/ \E p \in {1, 2} : l2(p)

Spec == Spec
PSpec == P(spec_translation(pc_translation(pc), c_translation(c)))

pc_translation(pc) == [p \in {1, 2} |-> IF pc[p] = 1 THEN "NCS" ELSEIF pc[p] = 2 THEN "TRY" ELSE "CS"]
c_translation(c) == c

====================================================================