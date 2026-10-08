MODULE FastMutexSpec

EXTENDS Naturals, TLC

CONSTANTS M,N
ASSUME M \leq N

VARIABLES x,y,b,cs

ProcSet == 1..N
Class(i) == IF i <= M THEN 1 ELSE 2

(* --- Initialization --- *)
Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i ∈ ProcSet |-> FALSE]
  /\ cs = [i ∈ ProcSet |-> FALSE]

(* --- Actions for process i --- *)
Request(i) ==
  /\ i \in ProcSet
  /\ b[i] = FALSE
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<x,y,cs>>

Enter(i) ==
  /\ i \in ProcSet
  /\ b[i] = TRUE
  /\ (x = 0 \/ x = Class(i))
  /\ (\A j ∈ ProcSet : cs[j] = FALSE)
  /\ cs' = [cs EXCEPT ![i] = TRUE]
  /\ y' = i
  /\ x' = Class(i)
  /\ UNCHANGED <<b>>

Exit(i) ==
  /\ i \in ProcSet
  /\ cs[i] = TRUE
  /\ cs' = [cs EXCEPT ![i] = FALSE]
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<x,y>>

(* --- Next-state relation --- *)
Next ==
  \E i ∈ ProcSet :
    (Request(i) \/ Enter(i) \/ Exit(i))

(* --- Mutual exclusion invariant --- *)
MutualExclusion ==
  \A i,j ∈ ProcSet : (i # j) => ~(cs[i] /\ cs[j])

(* --- Liveness property: some process enters CS infinitely often --- *)
Liveness ==
  \E i ∈ ProcSet : [] <> cs[i]

(* --- Full specification --- *)
Spec == Init /\ [][Next]_<<x,y,b,cs>> /\ \A i ∈ ProcSet : WF_i(Next)

THEOREM Spec => MutualExclusion
THEOREM Spec => Liveness

END MODULE