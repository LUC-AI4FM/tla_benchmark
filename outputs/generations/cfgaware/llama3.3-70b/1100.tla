---------------------------- MODULE MutualExclusion ----------------------------
EXTENDS Integers, TLC

CONSTANT P1, P2
VARIABLE lock, pc1, pc2

TypeOK == (lock \in {P1, P2, NULL}) /\ 
          (pc1 \in {"nc", "l1", "cs"}) /\ 
          (pc2 \in {"nc", "l1", "cs"})

LockInv == (pc1 = "cs") => (lock = P1) /\ 
           (pc2 = "cs") => (lock = P2)

Spec == 
  /\ lock = NULL
  /\ pc1 = "nc"
  /\ pc2 = "nc"
  /\ [][
      /\ (pc1 = "nc" => 
          \/ /\ pc1' = "l1"
             /\ lock' = lock
             /\ pc2' = pc2
          \/ /\ pc1' = "cs"
             /\ lock' = P1
             /\ pc2' = pc2)
      /\ (pc1 = "l1" => 
          \/ /\ pc1' = "cs"
             /\ lock' = P1
             /\ pc2' = pc2
          \/ /\ pc1' = "l1"
             /\ lock' = lock
             /\ pc2' = pc2)
      /\ (pc1 = "cs" => 
          \/ /\ pc1' = "nc"
             /\ lock' = NULL
             /\ pc2' = pc2
          \/ /\ pc1' = "cs"
             /\ lock' = lock
             /\ pc2' = pc2)
      /\ (pc2 = "nc" => 
          \/ /\ pc2' = "l1"
             /\ lock' = lock
             /\ pc1' = pc1
          \/ /\ pc2' = "cs"
             /\ lock' = P2
             /\ pc1' = pc1)
      /\ (pc2 = "l1" => 
          \/ /\ pc2' = "cs"
             /\ lock' = P2
             /\ pc1' = pc1
          \/ /\ pc2' = "l1"
             /\ lock' = lock
             /\ pc1' = pc1)
      /\ (pc2 = "cs" => 
          \/ /\ pc2' = "nc"
             /\ lock' = NULL
             /\ pc1' = pc1
          \/ /\ pc2' = "cs"
             /\ lock' = lock
             /\ pc1' = pc1)
  ]

THEOREM Spec => []LockInv

THEOREM Spec => <>(pc1 = "l1") ~> <> (pc1 = "cs")
=============================================================================