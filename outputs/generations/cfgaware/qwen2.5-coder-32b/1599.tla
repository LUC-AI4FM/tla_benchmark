------------------------------- MODULE FastMutualExclusion -------------------------------
VARIABLES x, y, b

CONSTANTS N

ASSUME N \in Nat /\ N > 0

(*--algorithm fast_mutual_exclusion
variables x = 0, y = 0, b = [i \in 1..N -> FALSE];

process p \in 1..N
begin
    while TRUE do
        noncritical_section:
            skip;
        await_entry:
            b[p] := TRUE;
            x := p;
            await (y = 0 \/ y = p);
        critical_section:
            assert (\A q \in 1..N : q # p => ~b[q]);
            skip;
        exit_critical_section:
            y := 0;
            b[p] := FALSE;
end process;
end algorithm *)

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N -> FALSE]

Next ==
    \/ /\ \/ \E p \in 1..N : \/ /\ b' = [b EXCEPT ![p] = TRUE]
                                /\ x' = p
                                /\ y' = y
                           \/ /\ b' = b
                              /\ x' = x
                              /\ y' = 0
                  /\ \A q \in 1..N \ {p} : b[q] = b'[q]
        \/ /\ \/ \E p \in 1..N : \/ /\ b' = [b EXCEPT ![p] = FALSE]
                                /\ x' = x
                                /\ y' = y
                           \/ /\ b' = b
                              /\ x' = x
                              /\ y' = p
                  /\ \A q \in 1..N \ {p} : b[q] = b'[q]

Spec == Init /\ [][Next]_<<x, y, b>>

Invariant ==
    \A p, q \in 1..N : p # q => ~b[p] \/ ~b[q]

CondLiveness ==
    \A p \in 1..N : <>(\E q \in 1..N : b[q])

FairSpec ==
    Spec /\ WF_next(Next)

WF_next(action) == 
    \A S \subseteq action : S \in SF_next => <>[]\E a \in S : a

SF_next ==
    {S \in SUBSET Next :
        \E p \in 1..N, q \in 1..N \ {p} :
            (\E a \in S : /\ b' = [b EXCEPT ![p] = TRUE]
                           /\ x' = p
                           /\ y' = y)
            \/ (\E a \in S : /\ b' = [b EXCEPT ![p] = FALSE]
                           /\ x' = x
                           /\ y' = y)}

=============================================================================