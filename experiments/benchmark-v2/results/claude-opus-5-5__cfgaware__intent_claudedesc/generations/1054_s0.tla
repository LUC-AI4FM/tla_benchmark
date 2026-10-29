------------------------------- MODULE EWD426 -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, M

ASSUME NAssumption == N \in Nat \ {0}
ASSUME MAssumption == M \in Nat \ {0}
ASSUME RingAssumption == N <= M + 1

Node  == 0 .. N-1
Value == 0 .. M-1

VARIABLE c

vars == <<c>>

Pred(i) == IF i = 0 THEN N-1 ELSE i-1

TypeOK == c \in [Node -> Value]

Init == c \in [Node -> Value]

Privileged(i) ==
    IF i = 0 THEN c[0] = c[Pred(0)]
             ELSE c[i] # c[Pred(i)]

CreateToken(i) ==
    /\ i = 0
    /\ c[i] = c[Pred(i)]
    /\ c' = [c EXCEPT ![i] = (c[Pred(i)] + 1) % M]

PassToken(i) ==
    /\ i # 0
    /\ c[i] # c[Pred(i)]
    /\ c' = [c EXCEPT ![i] = c[Pred(i)]]

Act(i) == CreateToken(i) \/ PassToken(i)

Next == \E i \in Node : Act(i)

Fairness == \A i \in Node : WF_vars(Act(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Exactly one token: a unique position i where the counter values         *)
(* transition. Nodes 0..i-1 agree with c[0]; nodes i..N-1 hold the         *)
(* predecessor value c[0]-1 (mod M). i = N means all nodes agree, so only  *)
(* node 0 is privileged.                                                    *)
-----------------------------------------------------------------------------
PrevVal(v) == (v + M - 1) % M

UniqueToken ==
    \E i \in 1 .. N :
        /\ \A j \in 0 .. (i-1) : c[j] = c[0]
        /\ \A j \in i .. (N-1) : c[j] = PrevVal(c[0])

Tokens == {i \in Node : Privileged(i)}

Stab == <>[]UniqueToken

Alias == [ c      |-> c,
           tokens |-> Tokens,
           unique |-> UniqueToken ]

=============================================================================