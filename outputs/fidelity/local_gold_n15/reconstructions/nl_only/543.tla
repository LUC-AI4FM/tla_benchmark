---- MODULE Session7fgCompanion ----
EXTENDS Integers, FiniteSets

CONSTANTS N, ProcSet

VARIABLES x, pc, t

Init == /\ x = 0
        /\ pc \in [ProcSet -> {"p1", "p2", "Done"}]
        /\ t \in [ProcSet -> BOOLEAN]

Next ==
    \/ /\ pc["A"] = "p1"
       /\ pc' = [pc EXCEPT !["A"] = "p2"]
       /\ x' = x + 1
       /\ t' = t
    \/ /\ pc["A"] = "p2"
       /\ pc' = [pc EXCEPT !["A"] = "Done"]
       /\ x' = x
       /\ t' = t
    \/ /\ pc["B"] = "p1"
       /\ pc' = [pc EXCEPT !["B"] = "p2"]
       /\ x' = x + 1
       /\ t' = t
    \/ /\ pc["B"] = "p2"
       /\ pc' = [pc EXCEPT !["B"] = "Done"]
       /\ x' = x
       /\ t' = t
    \/ /\ pc \in [ProcSet -> {"Done"}]
       /\ pc' = pc
       /\ x' = x
       /\ t' = t

TypeInvariant ==
    /\ x \in 0..N
    /\ pc \in [ProcSet -> {"p1", "p2", "Done"}]
    /\ t \in [ProcSet -> BOOLEAN]

AllDoneCondition ==
    \/ (\E p \in ProcSet : pc[p] /= "Done")
    \/ x = N

MutualExclusion ==
    LET ProcessPairs == { <<p, q>> \in (ProcSet \X ProcSet) : p <> q }
    IN  \A pp \in ProcessPairs :
            ~ ((pc[pp[1]] \in {"p1", "p2"}) /\ (pc[pp[2]] \in {"p1", "p2"}))

Spec ==
    Init /\ [][Next]_<<x, pc, t>> /\ WF_next(<<x, pc, t>>) /\
    TypeInvariant /\ AllDoneCondition /\ MutualExclusion
========================================