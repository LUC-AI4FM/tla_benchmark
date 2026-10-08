---------------------------- MODULE MutualExclusion ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Processes
VARIABLE lock, pc

TypeOK == (lock \in {"locked", "unlocked"}) /\ 
         (pc \in [Processes -> {"non_critical", "acquiring", "critical", "releasing"}])

LockInv == (lock = "locked") <=> (\E p \in Processes : pc[p] \in {"acquiring", "critical"})

Spec == 
  /\ lock = "unlocked"
  /\ pc = [p \in Processes |-> "non_critical"]
  /\ [][
      /\ \A p \in Processes :
          (pc[p] = "non_critical") => 
            (pc' = [pc EXCEPT ![p] = "acquiring"]) \/ (pc' = pc)
        /\ (pc[p] = "acquiring") => 
            (lock = "unlocked" => (pc' = [pc EXCEPT ![p] = "critical"] /\ lock' = "locked")) \/ 
            (lock /= "unlocked" => pc' = pc)
        /\ (pc[p] = "critical") => 
            (pc' = [pc EXCEPT ![p] = "releasing"]) \/ (pc' = pc)
        /\ (pc[p] = "releasing") => 
            (pc' = [pc EXCEPT ![p] = "non_critical"] /\ lock' = "unlocked") \/ (pc' = pc)
      /\ lock' \in {"locked", "unlocked"}
      /\ TypeOK'
  ]

THEOREM Spec => []TypeOK
THEOREM Spec => []LockInv

=============================================================================