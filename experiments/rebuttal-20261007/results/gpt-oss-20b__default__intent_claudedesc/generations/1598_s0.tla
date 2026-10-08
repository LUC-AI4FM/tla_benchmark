MODULE LamportFastMutex
EXTENDS Integers

CONSTANT N

VARIABLES x, y, b, cs

vars == <<x, y, b, cs>>

TypeInvariant ==
  /\ x \in Integers
  /\ y \in Integers
  /\ b \in [1..N -> BOOLEAN]
  /\ cs \in [1..N -> BOOLEAN]

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ cs = [i \in 1..N |-> FALSE]
  /\ TypeInvariant

SetFlag(i) ==
  /\ i \in 1..N
  /\ b[i] = FALSE
  /\ cs[i] = FALSE
  /\ y = 0
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<x, y, cs>>

WriteX(i) ==
  /\ i \in 1..N
  /\ b[i] = TRUE
  /\ x' = i
  /\ UNCHANGED <<y, b, cs>>

CheckYBackoff(i) ==
  /\ i \in 1..N
  /\ b[i] = TRUE
  /\ y # 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<x, y, cs>>

WriteY(i) ==
  /\ i \in 1..N
  /\ b[i] = TRUE
  /\ y' = i
  /\ UNCHANGED <<x, b, cs>>

CheckXBackoff(i) ==
  /\ i \in 1..N
  /\ b[i] = TRUE
  /\ x # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<x, y, cs>>

EnterCS(i) ==
  /\ i \in 1..N
  /\ b[i] = TRUE
  /\ x = i
  /\ y = i
  /\ cs' = [cs EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<x, y, b>>

ExitCS(i) ==
  /\ i \in 1..N
  /\ cs[i] = TRUE
  /\ cs' = [cs EXCEPT ![i] = FALSE]
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<x>>

Next ==
  \E i \in 1..N :
    SetFlag(i) \/ WriteX(i) \/ CheckYBackoff(i) \/ 
    WriteY(i) \/ CheckXBackoff(i) \/ EnterCS(i) \/ ExitCS(i)

MutualExclusion ==
  \A i, j \in 1..N : (i # j) => ~(cs[i] /\ cs[j])

EnterCSAll == \E i \in 1..N : EnterCS(i)

Spec ==
  Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
  /\ MutualExclusion
  /\ WF_action(EnterCSAll)

END MODULE