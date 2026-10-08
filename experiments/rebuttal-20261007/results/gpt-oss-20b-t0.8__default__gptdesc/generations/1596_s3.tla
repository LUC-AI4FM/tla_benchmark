MODULE FastMutexSpec
EXTENDS Naturals, Sequences, TLC, Temporal

CONSTANTS N, M
ASSUME M <= N

PROC_SET == 1 .. N
CLASS_1   == 1 .. M
CLASS_2   == (M + 1) .. N

VARIABLES x, y, b, pc

TypeInvariant ==
  /\ x \in Nat ∪ {0}
  /\ y \in Nat ∪ {0}
  /\ b \in BOOLEAN
  /\ pc \in [PROC_SET -> {"idle","waiting1","critical"}]

Init ==
  /\ TypeInvariant
  /\ x = 0
  /\ y = 0
  /\ b = FALSE
  /\ \A i ∈ PROC_SET : pc[i] = "idle"

(* Actions for class 1 *)
Request1(i) == 
  /\ i ∈ CLASS_1
  /\ pc[i] = "idle"
  /\ x' = i
  /\ pc'[i] = "waiting1"

EnterCritical1(i) ==
  /\ i ∈ CLASS_1
  /\ pc[i] = "waiting1"
  /\ y = 0
  /\ b = FALSE
  /\ b' = TRUE
  /\ pc'[i] = "critical"

Exit1(i) ==
  /\ i ∈ CLASS_1
  /\ pc[i] = "critical"
  /\ x' = 0
  /\ b' = FALSE
  /\ pc'[i] = "idle"

(* Actions for class 2 *)
Request2(i) == 
  /\ i ∈ CLASS_2
  /\ pc[i] = "idle"
  /\ y' = i
  /\ pc'[i] = "waiting1"

EnterCritical2(i) ==
  /\ i ∈ CLASS_2
  /\ pc[i] = "waiting1"
  /\ x = 0
  /\ b = FALSE
  /\ b' = TRUE
  /\ pc'[i] = "critical"

Exit2(i) ==
  /\ i ∈ CLASS_2
  /\ pc[i] = "critical"
  /\ y' = 0
  /\ b' = FALSE
  /\ pc'[i] = "idle"

Next ==
  \E i ∈ PROC_SET :
    (Request1(i) \/ EnterCritical1(i) \/ Exit1(i) \/
     Request2(i) \/ EnterCritical2(i) \/ Exit2(i))

Class1Action == 
  \E i ∈ CLASS_1 : (Request1(i) \/ EnterCritical1(i) \/ Exit1(i))

Class2Action == 
  \E i ∈ CLASS_2 : (Request2(i) \/ EnterCritical2(i) \/ Exit2(i))

MutualExcl ==
  \A i, j ∈ PROC_SET :
    (i # j) => ~(pc[i] = "critical" /\ pc[j] = "critical")

Liveness ==
  \E i ∈ PROC_SET : []◇(pc[i] = "critical")

Spec ==
  Init
  /\ [][Next]_vars
  /\ WF_Action(Class1Action)
  /\ WF_Action(Class2Action)
  /\ MutualExcl

THEOREM LivenessProp == Spec => Liveness

====