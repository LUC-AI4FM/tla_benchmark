------------------------------- MODULE ByzantineConsensus -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Procs \* N > 3T >= 3F >= 0

VARIABLES pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty

Init == /\ pc = [p \in Procs |-> IF p \notin (CHOOSE f \in SUBSET Procs : Cardinality(f) = F) THEN "V0" ELSE "BYZ"]
        /\ nSnt0 = 0
        /\ nSnt1 = 0
        /\ nSnt0F = 0
        /\ nSnt1F = 0
        /\ nRcvd0 = [p \in Procs |-> 0]
        /\ nRcvd1 = [p \in Procs |-> 0]
        /\ nFaulty = 0

Propose ==
    \E p \in Procs : pc[p] \in {"V0", "V1"} /\ 
                      (pc' = [pc EXCEPT ![p] = IF pc[p] = "V0" THEN "S0" ELSE "S1"]) /\
                      (nSnt0' = IF pc[p] = "V0" THEN nSnt0 + 1 ELSE nSnt0) /\
                      (nSnt1' = IF pc[p] = "V1" THEN nSnt1 + 1 ELSE nSnt1) /\
                      UNCHANGED <<nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>

Receive ==
    \E p \in Procs : pc[p] \in {"S0", "S1"} /\ 
                      (nRcvd0' = [nRcvd0 EXCEPT ![p] = Min(nRcvd0[p] + 1, nSnt0 + nSnt0F)]) /\
                      (nRcvd1' = [nRcvd1 EXCEPT ![p] = Min(nRcvd1[p] + 1, nSnt1 + nSnt1F)]) /\
                      UNCHANGED <<pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty>>

Decide ==
    \E p \in Procs : pc[p] \in {"S0", "S1"} /\ 
                      (nRcvd0[p] >= N - T \/ nRcvd1[p] >= N - T) /\
                      (pc' = [pc EXCEPT ![p] = IF nRcvd0[p] >= N - T THEN "D0" ELSE IF nRcvd1[p] >= N - T THEN "D1" ELSE IF pc[p] = "S0" THEN "U0" ELSE "U1"]) /\
                      UNCHANGED <<nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>

Faulty ==
    \E p \in Procs : pc[p] \notin {"BYZ"} /\ nFaulty < F /\
                      (pc' = [pc EXCEPT ![p] = "BYZ"]) /\
                      (nFaulty' = nFaulty + 1) /\
                      UNCHANGED <<nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1>>

Next == Propose \/ Receive \/ Decide \/ Faulty

Spec ==
    /\ Init
    /\ [][Next]_<<pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>
    /\ WF_[Propose]_<<pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>
    /\ WF_[Receive]_<<pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>
    /\ WF_[Decide]_<<pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>

TypeOK ==
    /\ \A p \in Procs : pc[p] \in {"V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1", "BYZ"}
    /\ nSnt0 >= 0
    /\ nSnt1 >= 0
    /\ nSnt0F >= 0
    /\ nSnt1F >= 0
    /\ \A p \in Procs : nRcvd0[p] >= 0
    /\ \A p \in Procs : nRcvd1[p] >= 0
    /\ nFaulty >= 0

Invariant ==
    TypeOK

ValidityPropose0 ==
    [](pc["V0"] => []~(pc["U0"] \/ pc["D1"]))

ValidityPropose1 ==
    <>(pc["V1"] => <>[]~(pc["U1"] \/ pc["D0"]))

AllDecideOne ==
    <>(\A p \in Procs : pc[p] = "D1")

=============================================================================