------------------------------- MODULE FastMutualExclusion -------------------------------
VARIABLES x, y, b, j

CONSTANTS N

ASSUME N \in Nat /\ N > 0

vars == <<x, y, b, j>>

defaultInitValue == <<1, 1, [i \in 1..N -> FALSE], [i \in 1..N -> 1]>>

Init == 
    /\ x = 1
    /\ y = 1
    /\ \A i \in 1..N : b[i] = FALSE
    /\ \A i \in 1..N : j[i] = 1

(*--algorithm FastMutualExclusion
variables x=1, y=1, b[N]={FALSE}, j[N]={1};

process (p \in 1..N)
begin
Entry:
    while (x # p) \/ (\E q \in 1..N : q # p /\ b[q])
        j[p] := (j[p] + 1) % N;
        x := p;
        y := j[p];
        b[p] := TRUE;
        await (y = j[p]) /\ (\A q \in 1..N \ {p} : ~b[q]);
    end while;

CriticalSection:
    skip;

Exit:
    b[p] := FALSE;
end process;
\*--algorithm *)

Next == 
    \E p \in 1..N :
        \/ /\ x # p \/ (\E q \in 1..N : q # p /\ b[q])
           /\ j' = [j EXCEPT ![p] = (j[p] + 1) % N]
           /\ x' = p
           /\ y' = j'[p]
           /\ b' = [b EXCEPT ![p] = TRUE]
        \/ /\ y = j[p] /\ (\A q \in 1..N \ {p} : ~b[q])
           /\ b' = [b EXCEPT ![p] = FALSE]

Spec == 
    /\ Init
    /\ [][Next]_<<x, y, b, j>>
    /\ WF_next(<<x, y, b, j>>)

Invariant ==
    \/ \A p \in 1..N : ~b[p]
    \/ \E p \in 1..N : b[p] /\ (\A q \in 1..N \ {p} : ~b[q])

Liveness ==
    <>[](\E p \in 1..N : y = j[p] /\ (\A q \in 1..N \ {p} : ~b[q]))

=============================================================================