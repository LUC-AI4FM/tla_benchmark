```tla
------------------------------- MODULE DiningPhilosophers -------------------------------
CONSTANTS N

VARIABLES sem, pc

(*--algorithm dining_philosophers
variables 
    sem = <<1, 1, 1, 1>>, 
    pc = [i \in 0..N-1 |-> "l01"]

process (Philosopher = i) \in 0..N-1
begin
    if i = 0 then
        l01: while TRUE do
            await sem[i] = 1;
            sem[i] := 0;
            l02: await sem[(i + N - 1) % N] = 1;
            sem[(i + N - 1) % N] := 0;
            l03: skip;  \* eat
            l04: sem[i] := 1;
            sem[(i + N - 1) % N] := 1;
        end while;
    else
        l1: while TRUE do
            await sem[i] = 1;
            sem[i] := 0;
            l2: await sem[(i + 1) % N] = 1;
            sem[(i + 1) % N] := 0;
            l3: skip;  \* eat
            l4: sem[i] := 1;
            sem[(i + 1) % N] := 1;
        end while;
    end if;
end process;

Spec ==
    /\ Init
    /\ [][Next]_<<sem, pc>>
    /\ WF_pc(0)
    /\ SF_pc(0)
    /\ WF_pc(1)
    /\ SF_pc(1)
    /\ WF_pc(2)
    /\ SF_pc(3)

Init ==
    /\ sem = <<1, 1, 1, 1>>
    /\ pc = [i \in 0..N-1 |-> IF i = 0 THEN "l01" ELSE "l1"]

Next ==
    \/ \E i \in 0..N-1 : (pc[i] = "l01" /\ sem[i] = 1 /\ sem[(i + N - 1) % N] = 1
                            /\ pc' = [pc EXCEPT ![i] = "l03"]
                            /\ sem' = [sem EXCEPT ![i] = 0, ![(i + N - 1) % N] = 0])
    \/ \E i \in 0..N-1 : (pc[i] = "l02" /\ sem[(i + N - 1) % N] = 1
                            /\ pc' = [pc EXCEPT ![i] = "l03"]
                            /\ sem' = [sem EXCEPT ![(i + N - 1) % N] = 0])
    \/ \E i \in 0..N-1 : (pc[i] = "l03"
                            /\ pc' = [pc EXCEPT ![i] = "l04"])
    \/ \E i \in 0..N-1 : (pc[i] = "l04"
                            /\ pc' = [pc EXCEPT ![i] = "l01"]
                            /\ sem' = [sem EXCEPT ![i] = 1, ![(i + N - 1) % N] = 1])
    \/ \E i \in 1..N-1 : (pc[i] = "l1" /\ sem[i] = 1
                           /\ pc' = [pc EXCEPT ![i] = "l2"]
                           /\ sem' = [sem EXCEPT ![i] = 0])
    \/ \E i \in 1..N-1 : (pc[i] = "l2" /\ sem[(i + 1) % N] = 1
                           /\ pc' = [pc EXCEPT ![i] = "l3"]
                           /\ sem' = [sem EXCEPT ![(i + 1) % N] = 0])
    \/ \E i \in 1..N-1 : (pc[i] = "l3"
                           /\ pc' = [pc EXCEPT ![i] = "l4"])
    \/ \E i \in 1..N-1 : (pc[i] = "l4"
                           /\ pc' = [pc EXCEPT ![i] = "l1"]
                           /\ sem' = [sem EXCEPT ![i] = 1, ![(i + 1) % N] = 1])

Invariant ==
    \A i \in 0..N-1 : ~(\E j \in {i, (i + 1) % N} : pc[j] = IF j = 0 THEN "l03" ELSE "l3")

StarvationFree ==
    \A i \in 0..N-1 : [](<>[]pc[i] = IF i = 0 THEN "l03" ELSE "l3")
    
WF_pc(i) == 
    /\ pc[i] \in {"l01", "l02", "l03", "l04"} \/ (i > 0 /\ pc[i] \in {"l1", "l2", "l3", "l4"})
    /\ [](pc[i] = IF i = 0 THEN "l01" ELSE "l1" => <>[]<>pc[i] = IF i = 0 THEN "l03" ELSE "l3")

SF_pc(i) ==
    WF_pc(i)
    /\ [](pc[i] = IF i = 0 THEN "l01" ELSE "l1" => <>[]<>pc[i] = IF i = 0 THEN "l03" ELSE "l3")
    
end algorithm
```

This TLA+ specification captures the classic asymmetric solution to the Dining Philosophers problem for N philosophers arranged in a circle, with the specified initial conditions, next-state relation, safety invariant, and liveness property. The model is configured for N = 4 as required.