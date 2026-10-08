------------------------------- MODULE TwoProcessLock -------------------------------
EXTENDS Naturals

CONSTANT P1 = 1, P2 = 2

VARIABLES lock, pc1, pc2

vars == {lock, pc1, pc2}

Init ==
    /\ lock = 0
    /\ pc1 = "nc"
    /\ pc2 = "nc"

Proc1Step ==
    \/ /\ pc1 = "nc" 
       /\ pc1' = "l1"
       /\ lock' = lock
       /\ pc2' = pc2
    \/ /\ pc1 = "l1" /\ lock = 0
       /\ pc1' = "cs"
       /\ lock' = P1
       /\ pc2' = pc2
    \/ /\ pc1 = "l1" /\ lock # 0
       /\ pc1' = "l1"
       /\ lock' = lock
       /\ pc2' = pc2
    \/ /\ pc1 = "cs" /\ lock = P1
       /\ pc1' = "nc"
       /\ lock' = 0
       /\ pc2' = pc2

Proc2Step ==
    \/ /\ pc2 = "nc"
       /\ pc2' = "l2"
       /\ lock' = lock
       /\ pc1' = pc1
    \/ /\ pc2 = "l2" /\ lock = 0
       /\ pc2' = "cs"
       /\ lock' = P2
       /\ pc1' = pc1
    \/ /\ pc2 = "l2" /\ lock # 0
       /\ pc2' = "l2"
       /\ lock' = lock
       /\ pc1' = pc1
    \/ /\ pc2 = "cs" /\ lock = P2
       /\ pc2' = "nc"
       /\ lock' = 0
       /\ pc1' = pc1

Next == Proc1Step \/ Proc2Step

Spec == Init /\ [][Next]_(vars)

MutualExcl ==
    ~ (pc1 = "cs" /\ pc2 = "cs")
    /\ ((lock = P1) <=> (pc1 = "cs"))
    /\ ((lock = P2) <=> (pc2 = "cs"))

Liveness == [](pc1 = "l1" => <> (pc1 = "cs"))

THEOREM MutualExclusion_Inv: Spec => []MutualExcl
THEOREM LivenessProp: Spec => Liveness

=============================================================================