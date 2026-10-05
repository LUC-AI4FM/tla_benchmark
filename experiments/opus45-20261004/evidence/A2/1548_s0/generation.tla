---------------------------- MODULE ByzantineConsensus ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F

ASSUME /\ N > 3 * T
       /\ 3 * T >= 3 * F
       /\ 3 * F >= 0
       /\ N > 0

Proc == 1..N

Status == {"V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1", "BYZ"}

VARIABLES
    pc,
    nSnt0,
    nSnt1,
    nSnt0F,
    nSnt1F,
    nRcvd0,
    nRcvd1,
    nFaulty

vars == <<pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>

TypeOK ==
    /\ pc \in [Proc -> Status]
    /\ nSnt0 \in 0..N
    /\ nSnt1 \in 0..N
    /\ nSnt0F \in 0..N
    /\ nSnt1F \in 0..N
    /\ nRcvd0 \in [Proc -> 0..N]
    /\ nRcvd1 \in [Proc -> 0..N]
    /\ nFaulty \in 0..N

Init ==
    /\ pc \in [Proc -> {"V0", "V1"}]
    /\ nSnt0 = 0
    /\ nSnt1 = 0
    /\ nSnt0F = 0
    /\ nSnt1F = 0
    /\ nRcvd0 = [p \in Proc |-> 0]
    /\ nRcvd1 = [p \in Proc |-> 0]
    /\ nFaulty = 0

Propose(p) ==
    /\ pc[p] \in {"V0", "V1"}
    /\ IF pc[p] = "V0"
       THEN /\ pc' = [pc EXCEPT ![p] = "S0"]
            /\ nSnt0' = nSnt0 + 1
            /\ nSnt1' = nSnt1
       ELSE /\ pc' = [pc EXCEPT ![p] = "S1"]
            /\ nSnt1' = nSnt1 + 1
            /\ nSnt0' = nSnt0
    /\ UNCHANGED <<nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>

Receive(p) ==
    /\ pc[p] \notin {"BYZ"}
    /\ \/ /\ nRcvd0[p] < nSnt0 + nSnt0F
          /\ nRcvd0' = [nRcvd0 EXCEPT ![p] = nRcvd0[p] + 1]
          /\ UNCHANGED nRcvd1
       \/ /\ nRcvd1[p] < nSnt1 + nSnt1F
          /\ nRcvd1' = [nRcvd1 EXCEPT ![p] = nRcvd1[p] + 1]
          /\ UNCHANGED nRcvd0
    /\ UNCHANGED <<pc, nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty>>

Decide(p) ==
    /\ pc[p] \in {"S0", "S1"}
    /\ nRcvd0[p] + nRcvd1[p] >= N - T
    /\ IF nRcvd0[p] >= N - T
       THEN pc' = [pc EXCEPT ![p] = "D0"]
       ELSE IF nRcvd1[p] >= N - T
            THEN pc' = [pc EXCEPT ![p] = "D1"]
            ELSE IF pc[p] = "S0"
                 THEN pc' = [pc EXCEPT ![p] = "U0"]
                 ELSE pc' = [pc EXCEPT ![p] = "U1"]
    /\ UNCHANGED <<nSnt0, nSnt1, nSnt0F, nSnt1F, nRcvd0, nRcvd1, nFaulty>>

Faulty(p) ==
    /\ pc[p] # "BYZ"
    /\ nFaulty < F
    /\ pc' = [pc EXCEPT ![p] = "BYZ"]
    /\ nFaulty' = nFaulty + 1
    /\ \E inc0 \in 0..(N - nSnt0F) : \E inc1 \in 0..(N - nSnt1F) :
         /\ nSnt0F' = nSnt0F + inc0
         /\ nSnt1F' = nSnt1F + inc1
    /\ UNCHANGED <<nSnt0, nSnt1, nRcvd0, nRcvd1>>

ProposeAction == \E p \in Proc : Propose(p)
ReceiveAction == \E p \in Proc : Receive(p)
DecideAction == \E p \in Proc : Decide(p)
FaultyAction == \E p \in Proc : Faulty(p)

Next ==
    \/ ProposeAction
    \/ ReceiveAction
    \/ DecideAction
    \/ FaultyAction

Fairness ==
    /\ WF_vars(ProposeAction)
    /\ WF_vars(ReceiveAction)
    /\ WF_vars(DecideAction)

Spec == Init /\ [][Next]_vars /\ Fairness

AllInitiallyZero == \A p \in Proc : pc[p] = "V0"

AllInitiallyOne == \A p \in Proc : pc[p] = "V1"

NoUndecidedOrDecideOne ==
    \A p \in Proc : pc[p] \notin {"U0", "U1", "D1"}

NoUndecidedOrDecideZero ==
    \A p \in Proc : pc[p] \notin {"U0", "U1", "D0"}

Validity0 ==
    AllInitiallyZero => []NoUndecidedOrDecideOne

Validity1 ==
    AllInitiallyOne => <>NoUndecidedOrDecideZero

AllDecideOne ==
    <>(\A p \in Proc : pc[p] = "D1" \/ pc[p] = "BYZ")

===================================================================================