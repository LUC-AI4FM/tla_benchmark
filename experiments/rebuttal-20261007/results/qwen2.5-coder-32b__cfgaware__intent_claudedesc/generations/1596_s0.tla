------------------------------- MODULE FastMutualExclusion -------------------------------
CONSTANTS N, M

ASSUME 1 <= M /\ M < N

VARIABLES flag, turn, victim, cs

(*--algorithm fast_mutual_exclusion
variables 
    flag = [i \in 1..N -> FALSE],
    turn = 0,
    victim = 0;

process (P \in 1..M)
begin
    while TRUE do
        flag[P] := TRUE;
        victim := P;
        await \A i \in {j \in 1..N : j # P} : \neg flag[i] \/ turn # P \/ victim # i;
        /\* Critical Section *\
        flag[P] := FALSE;
    end while
end process

process (Q \in M+1..N)
begin
    while TRUE do
        flag[Q] := TRUE;
        victim := Q;
        await \A i \in {j \in 1..N : j # Q} : \neg flag[i] \/ turn # Q \/ victim # i;
        /\* Critical Section *\
        flag[Q] := FALSE;
    end while
end process

end algorithm*)

Spec == 
    /\ Init
    /\ [][Next]_<<flag, turn, victim>>
    /\ WF_next(<<flag, turn, victim>>)

Init ==
    /\ flag = [i \in 1..N -> FALSE]
    /\ turn = 0
    /\ victim = 0

Next ==
    \/ \E P \in 1..M : NextP(P)
    \/ \E Q \in M+1..N : NextQ(Q)

NextP(P) ==
    \/ /\ flag' = [flag EXCEPT ![P] = TRUE]
       /\ turn' = turn
       /\ victim' = P
       /\ UNCHANGED cs
    \/ /\ flag[P] 
       /\ (\A i \in {j \in 1..N : j # P} : \neg flag[i] \/ turn # P \/ victim # i)
       -> flag' = [flag EXCEPT ![P] = FALSE]
          /\ turn' = turn
          /\ victim' = victim
          /\ UNCHANGED cs

NextQ(Q) ==
    \/ /\ flag' = [flag EXCEPT ![Q] = TRUE]
       /\ turn' = turn
       /\ victim' = Q
       /\ UNCHANGED cs
    \/ /\ flag[Q] 
       /\ (\A i \in {j \in 1..N : j # Q} : \neg flag[i] \/ turn # Q \/ victim # i)
       -> flag' = [flag EXCEPT ![Q] = FALSE]
          /\ turn' = turn
          /\ victim' = victim
          /\ UNCHANGED cs

WF_next(vars) == WF_vars(Next, vars)

Invariant ==
    \A i, j \in 1..N : i # j => \/ ~flag[i] \/ ~flag[j]

Liveness ==
    <>[] (\E P \in 1..M : flag[P]) \/ (\E Q \in M+1..N : flag[Q])

=============================================================================