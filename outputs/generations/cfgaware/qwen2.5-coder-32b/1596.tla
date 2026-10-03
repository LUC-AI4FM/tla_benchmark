------------------------------- MODULE FastMutex -------------------------------

CONSTANTS N, M

VARIABLES x, y, b, pc

(*--algorithm FastMutex
variables x = 0, y = 0, b = [1..N -> FALSE], pc = [1..N -> "entry"]

process (p \in 1..M)
begin
entry:
    while TRUE do
        x := p;
        await (\A q \in 1..N : \neg (b[q] /\ y = p));
        b[p] := TRUE;
        await y = 0;
        y := p;
        await (\A q \in 1..N \ {p} : \neg b[q]);
    critical:
        skip;
    exit:
        b[p] := FALSE;
        if x = p then
            y := 0;
        end if;
end process;

process (p \in M+1..N)
begin
entry:
    while TRUE do
        x := p;
        await (\A q \in 1..N : \neg (b[q] /\ y = p));
        b[p] := TRUE;
        await y = 0;
        y := p;
        await (\A q \in 1..N \ {p} : \neg b[q]);
    critical:
        skip;
    exit:
        b[p] := FALSE;
        if x = p then
            y := 0;
        end if;
end process;

end algorithm *)

Init == /\ x = 0 
        /\ y = 0 
        /\ b = [1..N -> FALSE]
        /\ pc = [1..N -> "entry"]

Next ==
    \/ \E p \in 1..M : (pc[p] = "entry" /\ entry(p))
     \/ \E p \in M+1..N : (pc[p] = "entry" /\ entry(p))
     \/ \E p \in 1..M : (pc[p] = "critical" /\ critical(p))
     \/ \E p \in M+1..N : (pc[p] = "critical" /\ critical(p))
     \/ \E p \in 1..M : (pc[p] = "exit" /\ exit(p))
     \/ \E p \in M+1..N : (pc[p] = "exit" /\ exit(p))

entry(p) ==
    /\ x' = p
    /\ y' = y
    /\ b' = [b EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = IF \A q \in 1..N : \neg (b[q] /\ y = p) THEN "critical" ELSE "entry"]
    
critical(p) ==
    /\ x' = x
    /\ y' = y
    /\ b' = b
    /\ pc' = [pc EXCEPT ![p] = IF \A q \in 1..N \ {p} : \neg b[q] THEN "exit" ELSE "critical"]

exit(p) ==
    /\ x' = IF x = p THEN 0 ELSE x
    /\ y' = IF x = p THEN 0 ELSE y
    /\ b' = [b EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "entry"]

Spec == Init /\ [][Next]_<<x, y, b, pc>>

Invariant ==
    \A p1, p2 \in 1..N : p1 # p2 => ~(\A q \in 1..N : \neg (b[q] /\ y = p1) /\ b[p2])

Liveness ==
    <>[] (\E p \in 1..N : pc[p] = "critical")

=============================================================================