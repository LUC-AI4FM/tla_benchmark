---------------------------- MODULE MutualExclusion ----------------------------
EXTENDS Integers, TLC

CONSTANT ProcSet
VARIABLE lock, pc

TypeOK == 
  /\ lock \in {0, 1}
  /\ pc[1] \in {"l0", "l1", "cs", "l2"}
  /\ pc[2] \in {"l0", "l1", "cs", "l2"}

LockInv == 
  /\ ~(pc[1] \in {"cs", "l2"} /\ pc[2] \in {"cs", "l2"})
  /\ (pc[1] \in {"cs", "l2"} \/ pc[2] \in {"cs", "l2"}) => lock = 0

Next == 
  (\E i \in ProcSet : 
    /\ pc[i] = "l0"
    /\ pc' = [pc EXCEPT ![i] = "l1"]
    /\ lock' = lock
  )
  \/ 
  (\E i \in ProcSet : 
    /\ pc[i] = "l1"
    /\ lock = 1
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ lock' = 0
  )
  \/ 
  (\E i \in ProcSet : 
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "l2"]
    /\ lock' = lock
  )
  \/ 
  (\E i \in ProcSet : 
    /\ pc[i] = "l2"
    /\ pc' = [pc EXCEPT ![i] = "l0"]
    /\ lock' = 1
  )

Spec == 
  /\ Init
  /\ [][Next]_<<lock, pc>>

Init == 
  /\ lock = 1
  /\ pc[1] = "l0"
  /\ pc[2] = "l0"

THEOREM Spec => []TypeOK
PROOF * 
  S1: TypeOK => Init
    OBVIOUS
  S2: TypeOK /\ [Next]_<<lock, pc>> => TypeOK'
    PROOF * 
      CASE pc[1] = "l0"
        CASE pc[2] = "l0" 
          THEN TypeOK' BY <1>1
        ...
      ...
      END CASE
    END PROOF
  S3: Spec => []TypeOK BY <1>2, S1, S2

THEOREM Spec => []LockInv
PROOF * 
  S1: LockInv => Init
    OBVIOUS
  S2: LockInv /\ [Next]_<<lock, pc>> => LockInv'
    PROOF * 
      CASE pc[1] = "l0"
        CASE pc[2] = "l0" 
          THEN LockInv' BY <2>1
        ...
      ...
      END CASE
    END PROOF
  S3: Spec => []LockInv BY <2>2, S1, S2

=============================================================================