------------------------------- MODULE FastMutualExclusion -------------------------------
EXTENDS Naturals, Sequences

CONSTANTS N \* Number of processes
ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b \* Shared variables

Proc == {p \in 1..N}

Init == 
    /\ x = 0 
    /\ y = 0 
    /\ b = <<FALSE>> ^ N

Next ==
    \/ \/ p \in Proc :
           \/ /\ x = 0
              /\ b' = [b EXCEPT ![p] = TRUE]
              /\ x' = p
              /\ y' = 0
              /\ UNCHANGED <<b[p+1..N], b[1..p-1]>>
           \/ /\ x = p 
              /\ y = 0
              /\ y' = p
              /\ UNCHANGED b
           \/ /\ \A q \in Proc : (q # p => ~b[q])
              /\ b' = [b EXCEPT ![p] = FALSE]
              /\ x' = 0
              /\ y' = 0
    \/ \/ p \in Proc :
           /\ x = p 
           /\ y = p
           /\ UNCHANGED b

Spec ==
    WF_<<Proc, {act \in Next : act}>> Spec

MutualExclusion == 
    \A p, q \in Proc : (p # q => ~(\E s \in StateTrace : s.x = p /\ s.y = p /\ s.x = q /\ s.y = q))

Spec ==
    /\ Init
    /\ [][Next]_<<x, y, b>>
    /\ Stable(Proc)(\A s \in StateTrace : MutualExclusion)

WFSpec == 
    WF_<<Proc, {act \in Next : act}>> (Spec)
    
Fairness ==
    SF_<<p \in Proc : <<p, {act \in Next : act}>>>> Spec

ConditionalLiveness ==
    \A p \in Proc :
        [](<>[](\E s \in StateTrace : s.x = p /\ s.y = p))

CompleteSpec ==
    Spec /\ Fairness /\ ConditionalLiveness
=============================================================================