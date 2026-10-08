---------------------------- MODULE DijkstraTokenRing ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N, M
VARIABLE c

TypeOK == (* Type invariant: all counters are within range *)
         \A i \in 0..N-1 : c[i] \in 0..M-1

CreateToken == (* Action to create a token at node 0 *)
               /\ c[0] = c[(N-1)]
               /\ c' = [c EXCEPT ![0] = (c[0] + 1) % M]

PassToken(i) == (* Action to pass the token from node i-1 to node i *)
                /\ i \in 1..N-1
                /\ c[i] # c[(i-1)]
                /\ c' = [c EXCEPT ![i] = c[(i-1)]]

Next == (* Overall next-state relation *)
       \/ \E i \in 1..N-1 : PassToken(i)
       \/ CreateToken

Spec == (* Temporal specification with weak fairness *)
       Init /\ [][Next]_c
      WF_c(Next)

Init == (* Initial state: any assignment of counter values *)
       \A i \in 0..N-1 : c[i] \in 0..M-1

Stab == (* Liveness property: the system eventually stabilizes with one token *)
       <>[]\E t \in 0..M-1 : 
         /\ \A i \in 0..N-1 : c[i] = t \/ c[i] = (t-1) % M
         /\ \A i \in 0..N-2 : c[i] = t => c[i+1] = (t-1) % M

THEOREM Spec => []TypeOK
THEOREM Spec => Stab
=============================================================================