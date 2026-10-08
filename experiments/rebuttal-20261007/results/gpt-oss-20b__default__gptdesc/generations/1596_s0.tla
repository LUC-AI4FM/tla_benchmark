MODULE FastMutexSpec
EXTENDS Naturals, TLC

CONSTANTS M, N

VARIABLES pc, cs, x, y, b

(* Type invariant *)
TypeInvariant == 
  /\ pc \in [1..N -> {"idle","try1","try2","cs"}]
  /\ cs \in [1..N -> BOOLEAN]
  /\ x \in BOOLEAN
  /\ y \in BOOLEAN
  /\ b \in BOOLEAN

Init ==
  /\ TypeInvariant
  /\ \A i \in 1..N : pc[i] = "idle"
  /\ \A i \in 1..N : cs[i] = FALSE
  /\ x = FALSE
  /\ y = FALSE
  /\ b = FALSE

Action(i) == 
  \/ (pc[i] = "idle" /\ pc' = [pc EXCEPT ![i] = "try1"] /\ x' = TRUE /\ UNCHANGED <<y,b,cs>>)
  \/ (pc[i] = "try1" /\ pc' = [pc EXCEPT ![i] = "try2"] /\ y' = TRUE /\ UNCHANGED <<x,b,cs>>)
  \/ (pc[i] = "try2" /\ x /\ y /\ b /\ pc' = [pc EXCEPT ![i] = "cs"] 
      /\ cs' = [cs EXCEPT ![i] = TRUE] /\ b' = FALSE /\ UNCHANGED <<x,y>>)
  \/ (pc[i] = "cs" /\ pc' = [pc EXCEPT ![i] = "idle"] 
      /\ cs' = [cs EXCEPT ![i] = FALSE] /\ x'=FALSE /\ y'=FALSE /\ UNCHANGED <<b>>)

Next == \E i \in 1..N : Action(i)

Spec == Init
        /\ [][Next]_<<pc,cs,x,y,b>>
        /\ WF_0 (i \in 1..M) Action(i)
        /\ WF_0 (i \in M+1..N) Action(i)

MutualExcl == 
  \A i,j \in 1..N : i /= j => ~(cs[i] /\ cs[j])

Liveness == []<>(\E i \in 1..N : cs[i])

ASSERT MutualExcl
ASSERT Liveness