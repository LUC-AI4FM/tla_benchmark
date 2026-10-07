```
MODULE MutualExclusion
EXTENDS Integers, FiniteSets

CONSTANTS P
VARIABLES lock, pc

Init == (lock = 1) ∧ (pc = [i \in P |-> "l0"])

Next == (\E i \in P : 
            (pc[i] = "l0") ∧ (pc' = [pc EXCEPT ![i] = "l1"]) ∧ (lock' = lock)
          ∨ (pc[i] = "l1") ∧ (lock = 1) ∧ (pc' = [pc EXCEPT ![i] = "cs"]) ∧ (lock' = 0)
          ∨ (pc[i] = "cs") ∧ (pc' = [pc EXCEPT ![i] = "l2"]) ∧ (lock' = lock)
          ∨ (pc[i] = "l2") ∧ (pc' = [pc EXCEPT ![i] = "l0"]) ∧ (lock' = 1))

Spec == Init ∧ [][Next]_<<lock, pc>>

TypeOK == (lock \in {0, 1}) ∧ (\A i \in P : pc[i] \in {"l0", "l1", "cs", "l2"})

LockInv == (\A i, j \in P : 
              (i # j) => ~((pc[i] \in {"cs", "l2"}) ∧ (pc[j] \in {"cs", "l2"}))) 
          ∧ (\A i \in P : (pc[i] \in {"cs", "l2"}) => (lock = 0))

THEOREM Spec => []TypeOK
THEOREM Spec => []LockInv

```
Note: The `P` constant represents the set of process indices, which is assumed to be `{1, 2}`. The `pc` variable is an array that maps each process index to its current program counter label. The `lock` variable is an integer representing the lock state (0 = locked, 1 = unlocked).