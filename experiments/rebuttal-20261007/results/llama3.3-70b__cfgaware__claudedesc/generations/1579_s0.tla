--------------------------- MODULE DijkstraTokenRing ---------------------------
EXTENDS Integers, FiniteSets

CONSTANT N, K
VARIABLE M, pc

SomeoneHoldsToken == \E i \in 0..N-1 : (i = 0 /\ M[0] = M[(N-1)]) \/ (i > 0 /\ M[i] # M[(i-1)])

EventuallyJustOneHoldsToken == <>[]~(SomeoneHoldsToken /\ \A i, j \in 0..N-1 : 
  ((i = 0 /\ M[0] = M[(N-1)]) \/ (i > 0 /\ M[i] # M[(i-1)])) /\
  ((j = 0 /\ M[0] = M[(N-1)]) \/ (j > 0 /\ M[j] # M[(j-1)])) 
  => i = j)

TypeOK == (* M is a function from 0..N-1 to 0..K-1 *)
         M \in [0..N-1 -> 0..K-1] /\
         pc \in [0..N-1 -> {>>"start", "done"}]

Next(i \in 0..N-1) == 
  IF pc[i] = "start" THEN
    (* Process i is at the start of its step *)
    /\ (i = 0 /\ M[0] = M[(N-1)]) \/ (i > 0 /\ M[i] # M[(i-1)])
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ IF i = 0 THEN 
        (* Process 0 increments its value modulo K *)
        M' = [M EXCEPT ![0] = (M[0] + 1) % K]
      ELSE 
        (* Other processes copy their left neighbor's value *)
        M' = [M EXCEPT ![i] = M[(i-1)]]
  ELSE
    (* Process i is at the end of its step *)
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ M' = M

Spec == 
  (* Initial condition: TypeOK and all processes are at their start state *)
  Init /\ [][Next(0) \/ Next(1) \/ ... \/ Next(N-1)]_M,pc
  (* Weak fairness for all processes *)
  /\ \A i \in 0..N-1 : WF_vars(Next(i))_M,pc

Init == TypeOK /\ \A i \in 0..N-1 : pc[i] = "start"

THEOREM Spec => []SomeoneHoldsToken
THEOREM Spec => EventuallyJustOneHoldsToken
=============================================================================