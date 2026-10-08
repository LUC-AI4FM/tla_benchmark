------------------------------- MODULE FastMutualExclusion -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, M
ASSUME 1 <= M /\ M < N

VARIABLES flag, turn, victim, inCS

Init == 
    /\ flag = [i \in 1..N -> FALSE]
    /\ turn = 0
    /\ victim = 0
    /\ inCS = {}

Next ==
    \/ \/ /\ E \in 1..M
           /\ ~flag[E] 
           /\ turn = 0
           /\ victim = 0
           /\ UNCHANGED <<flag, turn, victim>>
           /\ inCS' = {E}
       \/ /\ E \in 1..M
           /\ flag[E]
           /\ (turn = 0 \/ turn = E)
           /\ victim = 0
           /\ flag' = [flag EXCEPT ![E] = TRUE]
           /\ turn' = E
           /\ victim' = 0
           /\ UNCHANGED inCS
       \/ /\ E \in 1..M
           /\ flag[E]
           /\ turn = E
           /\ victim = 0
           /\ ~(\E j \in (1..N) \ {E} : flag[j])
           /\ flag' = [flag EXCEPT ![E] = FALSE]
           /\ turn' = 0
           /\ victim' = 0
           /\ inCS' = {E}
       \/ /\ E \in 1..M
           /\ flag[E]
           /\ turn = E
           /\ victim = 0
           /\ (\E j \in (1..N) \ {E} : flag[j])
           /\ victim' = E
           /\ UNCHANGED <<flag, turn>>
           /\ inCS' = {}
       \/ /\ E \in M+1..N
           /\ ~flag[E] 
           /\ turn = 0
           /\ victim = 0
           /\ UNCHANGED <<flag, turn, victim>>
           /\ inCS' = {E}
       \/ /\ E \in M+1..N
           /\ flag[E]
           /\ (turn = 0 \/ turn = E)
           /\ victim = 0
           /\ flag' = [flag EXCEPT ![E] = TRUE]
           /\ turn' = E
           /\ victim' = 0
           /\ UNCHANGED inCS
       \/ /\ E \in M+1..N
           /\ flag[E]
           /\ turn = E
           /\ victim = 0
           /\ ~(\E j \in (1..N) \ {E} : flag[j])
           /\ flag' = [flag EXCEPT ![E] = FALSE]
           /\ turn' = 0
           /\ victim' = 0
           /\ inCS' = {E}
       \/ /\ E \in M+1..N
           /\ flag[E]
           /\ turn = E
           /\ victim = 0
           /\ (\E j \in (1..N) \ {E} : flag[j])
           /\ victim' = E
           /\ UNCHANGED <<flag, turn>>
           /\ inCS' = {}

Spec ==
    WF_next(Next) /\ 
    Init /\ 
    [][Next]_<<flag, turn, victim, inCS>> /\ 
    <>(\E i \in 1..N : inCS = {i}) /\ 
    [](Cardinality(inCS) <= 1)

WF_next(next) == 
    WFpc(next)

=============================================================================