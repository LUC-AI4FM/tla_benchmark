```tla
---------------------------- MODULE LamportFastMutualExclusion ----------------------------

EXTENDS Integers, Sequences, TLC

CONSTANTS N \* Number of processes excluding the distinguished process 1

VARIABLES x, y, b, c, f \* Shared variables and control state

Init == 
  /\ x = <<2..N>> -> [p \in 2..N |-> TRUE]
  /\ y = 1
  /\ b = FALSE
  /\ c = [p \in 2..N |-> FALSE]
  /\ f = [p \in 2..N |-> FALSE]

Next == 
  \/ /\ y # 1
     /\ \/ \E p \in 2..N : x[p] = TRUE
        \/ b = TRUE
     /\ c' = c EXCEPT ![y] = TRUE
     /\ f' = f EXCEPT ![y] = FALSE
  \/ /\ \A p \in 2..N : c[p]
     /\ y' # 1
     /\ x' = x EXCEPT ![y'] = FALSE
     /\ b' = FALSE
     /\ \E q \in 2..N : f[q] => y' = q
  \/ /\ y # 1
     /\ b
     /\ x' = x EXCEPT ![y] = TRUE
     /\ c' = [p \in 2..N |-> FALSE]
     /\ f' = [p \in 2..N |-> FALSE]
     /\ b' = FALSE
     /\ y' = 1
  \/ /\ y = 1
     /\ \E p \in 2..N : ~f[p] /\ x[p] = TRUE => y' = p
  \/ /\ y = 1
     /\ \A p \in 2..N : f[p] \/ \A p \in 2..N : x[p] = FALSE => b' = TRUE

Spec == 
  /\ Init
  /\ [][Next]_<<x, y, b, c, f>>
  /\ WF_y(Next)
  /\ SF_x(Next)

MutualExclusion == 
  \/ y = 1
  \/ \A p \in 2..N : x[p] => y = p

Liveness ==
  <>[](\E p \in 1..N : c[p])

THEOREM Spec => []MutualExclusion /\ Liveness

END LamportFastMutualExclusion
```