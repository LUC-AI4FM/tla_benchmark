------------------------------ MODULE APTokenRing ------------------------------
(***************************************************************************)
(* Token ring protocol with Apalache-compatible type annotations.          *)
(* The behaviour is imported from the TokenRing module via INSTANCE.        *)
(***************************************************************************)
EXTENDS Integers

    ----------------------------- MODULE TokenRing -----------------------------
    (***********************************************************************)
    (* Dijkstra's self-stabilizing token ring with N nodes and counters    *)
    (* modulo M. Node 0 holds the token when c[0] = c[N-1]; node i > 0     *)
    (* holds the token when c[i] # c[i-1].                                 *)
    (***********************************************************************)
    EXTENDS Integers

    CONSTANTS N, M

    VARIABLE c

    Node == 0 .. N-1

    vars == << c >>

    TypeOK == c \in [Node -> 0 .. M-1]

    Init == c \in [Node -> 0 .. M-1]

    HasToken(i) ==
        IF i = 0 THEN c[0] = c[N-1]
                 ELSE c[i] # c[i-1]

    CreateToken ==
        /\ c[0] = c[N-1]
        /\ c' = [c EXCEPT ![0] = (c[N-1] + 1) % M]

    PassToken(i) ==
        /\ i # 0
        /\ c[i] # c[i-1]
        /\ c' = [c EXCEPT ![i] = c[i-1]]

    Next == CreateToken \/ \E i \in Node \ {0} : PassToken(i)

    Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

    UniqueToken == \E i \in Node : \A j \in Node : HasToken(j) <=> (j = i)

    Stabilization == <>[]UniqueToken
    =============================================================================