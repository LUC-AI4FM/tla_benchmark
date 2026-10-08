------------------------------ MODULE EWD426 ------------------------------
EXTENDS Integers

CONSTANTS N, M
ASSUME N <= M + 1

VARIABLE c

Predecessor(i) == (i - 1 + N) % N

CreateToken ==
    /\ c[0] = c[Predecessor(0)]
    /\ c' = [c EXCEPT ![0] = (c[0]+1) % M]

PassToken(i) ==
    /\ i \in 0 .. N-1
    /\ i > 0
    /\ c[i] # c[Predecessor(i)]
    /\ c' = [c EXCEPT ![i] = c[Predecessor(i)]]

Next == 
    CreateToken
    \/ ∃i \in 0 .. N-1 :
        (i > 0 /\ PassToken(i))

Init == c \in [0 .. N-1 -> 0 .. M-1]

TypeOK ==
    ∀i \in 0 .. N-1 : c[i] \in 0 .. M-1

OneToken(c) ==
    ∃i \in 0 .. N-1 :
        (∀j \in 0 .. i-1 : c[j] = c[0]) /\
        (∀k \in i .. N-1 : c[k] = ((c[0]-1)+M) % M)

Stab == <>[](OneToken(c))

Spec ==
    Init
    /\ [][Next]_c
    /\ WF_vars(Next)

=============================================================================