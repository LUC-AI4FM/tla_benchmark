---------------------------- MODULE SimpleLock ----------------------------
EXTENDS Integers

CONSTANT ProcessSet
VARIABLE lock, pc

TypeOK == (lock \in {0, 1}) /\ (pc[1] \in {"ncs", "acs", "cs", "pcs"}) /\ (pc[2] \in {"ncs", "acs", "cs", "pcs"})

LockInv == 
  \/ (lock = 0) 
  \/ (lock = 1 /\ (pc[1] = "cs" \/ pc[1] = "pcs") /\ (pc[2] = "cs" \/ pc[2] = "pcs"))

Spec ==
  /\ lock = 0
  /\ pc = [i \in ProcessSet |-> "ncs"]
  /\ [][
      /\ (pc[1] = "ncs")
        /\ (lock' = lock)
        /\ (pc' = [pc EXCEPT ![1] = "acs"])
      \/ (pc[2] = "ncs")
        /\ (lock' = lock)
        /\ (pc' = [pc EXCEPT ![2] = "acs"])
      \/ (pc[1] = "acs") 
        /\ (lock = 0) 
        /\ (lock' = 1)
        /\ (pc' = [pc EXCEPT ![1] = "cs"])
      \/ (pc[2] = "acs")
        /\ (lock = 0)
        /\ (lock' = 1)
        /\ (pc' = [pc EXCEPT ![2] = "cs"])
      \/ (pc[1] = "cs") 
        /\ (lock' = lock) 
        /\ (pc' = [pc EXCEPT ![1] = "pcs"])
      \/ (pc[2] = "cs")
        /\ (lock' = lock)
        /\ (pc' = [pc EXCEPT ![2] = "pcs"])
      \/ (pc[1] = "pcs") 
        /\ (lock' = 0) 
        /\ (pc' = [pc EXCEPT ![1] = "ncs"])
      \/ (pc[2] = "pcs")
        /\ (lock' = 0)
        /\ (pc' = [pc EXCEPT ![2] = "ncs"])
    ]

THEOREM Spec => []TypeOK
PROOF * 
  OBVIOUS
THEOREM Spec => []LockInv
PROOF * 
  BY induction, DECOMPOSED INTO:
    BASE CASE: LockInv IN Init
      PROVE LockInv IN Init BY * 
        OBVIOUS
    INDUCTIVE STEP: LockInv AND Spec IMPLIES LockInv' 
      PROVE LockInv AND Spec IMPLIES LockInv' BY * 
        CASES ON pc[1], pc[2]
          SUCCEED

=============================================================================