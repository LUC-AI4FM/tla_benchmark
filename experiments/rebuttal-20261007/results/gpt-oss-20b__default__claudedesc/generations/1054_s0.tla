MODULE DijkstraTokenRing
EXTENDS Naturals, Integers

CONSTANTS N, M

(* Assume N > 0 /\ M > 0 /\ N <= M + 1 *)

VARIABLE c

Init == 
    /\ c \in [0..N-1 -> 0..M-1]

CreateToken ==
    /\ c[0] = c[N-1]
    /\ c' = [c EXCEPT ![0] = (c[0]+1) % M]

PassToken(i) ==
    /\ i \in 1..N-1
    /\ c[i] # c[(i-1) % N]
    /\ c' = [c EXCEPT ![i] = c[(i-1) % N]]

Next == 
    CreateToken \/ \E i \in 1..N-1 : PassToken(i)

Spec == Init /\ [][Next]_c /\ WF_vars(Next)

TypeOK ==
    /\ c \in [0..N-1 -> 0..M-1]

OneToken(c) ==
    \E i \in 0..N-1 :
        /\ (\A j \in 0..i-1 : c[j] = c[0])
        /\ (\A k \in i..N-1 : c[k] = (c[0]-1) % M)

Stab == <>[]OneToken(c)