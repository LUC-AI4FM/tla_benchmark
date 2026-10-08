------------------------------- MODULE FastMutualExclusion -------------------------------
CONSTANTS N

VARIABLES x, y, b, pc

(*--algorithm fast_mutual_exclusion
variables 
    x \in 1..N,
    y = 0,
    b = [i \in 1..N -> FALSE],
    pc = [i \in 1..N |-> "entry"]

process (p \in 1..N)
begin
entry:
    while TRUE do
        await \neg b[p];
        b[p] := TRUE;
        x := p;
        if y # 0 then
            backoff: 
                while y # 0 do
                    await FALSE;
                endwhile;
        else
            y := p;
            if x = p then
                critical_section:
                    assert \neg (\E q \in (1..N) \ {p} : b[q] /\ \neg failed[q]);
                    y := 0;
                    b[p] := FALSE;
                    await FALSE;
            else
                backoff2: 
                    b[p] := FALSE;
                    while (\E q \in 1..N \ {p} : b[q]) do
                        await FALSE;
                    endwhile;
                    if y # p then
                        failed[p] := TRUE;
                        wait_for_clear:
                            while y # 0 do
                                await FALSE;
                            endwhile;
                    else
                        critical_section2:
                            assert \neg (\E q \in (1..N) \ {p} : b[q] /\ \neg failed[q]);
                            y := 0;
                            b[p] := FALSE;
                            failed[p] := FALSE;
                            await FALSE;
                    endif;
            endif;
        endif;
    endwhile;
end process;

end algorithm*)

Spec ==
    /\ \A p \in 1..N : pc[p] \in {"entry", "backoff", "critical_section", "backoff2", "wait_for_clear", "critical_section2"}
    /\ x \in 1..N
    /\ y \in 0..N
    /\ b \in [1..N -> BOOLEAN]
    /\ failed \in [1..N -> BOOLEAN]
    /\ Init
    /\ \A p \in 1..N : WF_vars(Process(p), <<x, y, b[p], pc[p]>>)

Init ==
    /\ x = 1
    /\ y = 0
    /\ \A i \in 1..N : b[i] = FALSE
    /\ \A i \in 1..N : failed[i] = FALSE

Process(p) ==
    case pc[p]
        ["entry"] -> 
            /\ \neg b[p]
            /\ b' = [b EXCEPT ![p] = TRUE]
            /\ x' = p
            /\ y # 0 -> pc'[p] = "backoff"
            [] y = 0 -> pc'[p] = "critical_section"
        ["backoff"] ->
            /\ y # 0
            /\ pc'[p] = "backoff"
        ["critical_section"] ->
            /\ x = p
            /\ y' = 0
            /\ b'[p] = FALSE
            /\ pc'[p] = "entry"
        ["backoff2"] ->
            /\ y = p
            /\ \E q \in 1..N \ {p} : b[q]
            /\ b'[p] = FALSE
            /\ pc'[p] = "wait_for_clear"
        ["wait_for_clear"] ->
            /\ \neg (\E q \in 1..N \ {p} : b[q])
            /\ y # p
            /\ failed'[p] = TRUE
            /\ pc'[p] = "entry"
        ["critical_section2"] ->
            /\ y = p
            /\ y' = 0
            /\ b'[p] = FALSE
            /\ failed'[p] = FALSE
            /\ pc'[p] = "entry"
    [] OTHER -> UNCHANGED <<x, y, b[p], pc[p]>>
    endcase

Invariant ==
    \A p1, p2 \in 1..N : p1 # p2 => \/ \neg (\neg failed[p1] /\ y = p1)
                                   \/ \neg (\neg failed[p2] /\ y = p2)

Liveness ==
    <>[] (\E p \in 1..N : \neg failed[p] /\ y = p)

SomeoneInCS ==
    \E p \in 1..N : \neg failed[p] /\ y = p

Contention ==
    \A p \in 1..N : b[p]

defaultInitValue == <<1, 0, [i \in 1..N |-> FALSE], [i \in 1..N |-> "entry"], [i \in 1..N |-> FALSE]>>

=============================================================================