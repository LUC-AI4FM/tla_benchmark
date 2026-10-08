------------------------------- MODULE ByzantineConsensus -------------------------------
CONSTANTS N, T, F

VARIABLES pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty

(* --algorithm ByzantineConsensus
variables 
    pc = [p \in 1..N -> IF p > N - F THEN "BYZ" ELSE CHOOSE v \in {"V0", "V1"}], 
    nSnt0 = 0, 
    nSnt1 = 0, 
    nSnt0F = 0, 
    nSnt1F = 0, 
    nRcvd0 = [p \in 1..N -> 0], 
    nRcvd1 = [p \in 1..N -> 0],
    nFaulty = 0;

fair process (p \in 1..N) \in
    while pc[p] \notin {"D0", "D1", "BYZ"} do
        either
            /\ pc[p] \in {"V0", "V1"}
            /\ if pc[p] = "V0" then nSnt0' = nSnt0 + 1 else nSnt1' = nSnt1 + 1
            /\ pc' = [pc EXCEPT ![p] = IF pc[p] = "V0" THEN "S0" ELSE "S1"]
        or
            /\ pc[p] \in {"S0", "S1"}
            /\ if pc[p] = "S0" then nRcvd0' = [nRcvd0 EXCEPT ![p] = MIN(nRcvd0[p] + 1, nSnt0 + nSnt0F)]
               else nRcvd1' = [nRcvd1 EXCEPT ![p] = MIN(nRcvd1[p] + 1, nSnt1 + nSnt1F)]
        or
            /\ pc[p] \in {"S0", "S1"}
            /\ \/ (nRcvd0[p] >= N - T) -> pc' = [pc EXCEPT ![p] = IF nRcvd0[p] > nRcvd1[p] THEN "D0" ELSE IF nRcvd1[p] > nRcvd0[p] THEN "D1" ELSE IF pc[p] = "S0" THEN "U0" ELSE "U1"]
               \/ (nRcvd1[p] >= N - T) -> pc' = [pc EXCEPT ![p] = IF nRcvd0[p] > nRcvd1[p] THEN "D0" ELSE IF nRcvd1[p] > nRcvd0[p] THEN "D1" ELSE IF pc[p] = "S0" THEN "U0" ELSE "U1"]
        or
            /\ pc[p] \notin {"BYZ"}
            /\ nFaulty < F
            /\ pc' = [pc EXCEPT ![p] = "BYZ"]
            /\ nFaulty' = nFaulty + 1

end algorithm *)

TypeOK == 
    /\ nSnt0 >= 0
    /\ nSnt1 >= 0
    /\ nSnt0F >= 0
    /\ nSnt1F >= 0
    /\ nFaulty >= 0
    /\ nFaulty <= F
    /\ \A p \in 1..N : 
        \/ pc[p] = "BYZ"
        \/ pc[p] \in {"V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1"}
        /\ nRcvd0[p] >= 0
        /\ nRcvd1[p] >= 0
        /\ nRcvd0[p] <= nSnt0 + nSnt0F
        /\ nRcvd1[p] <= nSnt1 + nSnt1F

OneStep0_Ltl == 
    [](pc[1] = "V0" => []<>(\A p \in 1..N : pc[p] \notin {"D1", "U0", "U1"}))

OneStep1_Ltl == 
    [](pc[1] = "V1" => <>[](\A p \in 1..N : pc[p] \notin {"D0", "U0", "U1"}))

AllDecideOne ==
    <>(\A p \in 1..N : pc[p] = "D1")

Spec == 
    /\ TypeOK
    /\ WF_vars(<<Propose, Receive, Decide>>)
    /\ OneStep0_Ltl
    /\ OneStep1_Ltl
    /\ AllDecideOne

Propose ==
    {p \in 1..N : pc[p] \in {"V0", "V1"}}

Receive ==
    {p \in 1..N : pc[p] \in {"S0", "S1"}}

Decide ==
    {p \in 1..N : pc[p] \in {"S0", "S1"} /\ (nRcvd0[p] >= N - T \/ nRcvd1[p] >= N - T)}

WF_vars(V) == 
    WF_vars_<<V>>[pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty]

=============================================================================