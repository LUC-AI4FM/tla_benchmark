---------------------------- MODULE OneStepByzantineConsensus ----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS N, T, F

ASSUME /\ N > 3 * T
       /\ T >= F
       /\ F >= 0
       /\ N > 0

Procs == 1..N

CorrectProcs == 1..(N - F)
ByzantineProcs == (N - F + 1)..N

VARIABLES
    proposal,
    hasSent,
    sentVotes0Correct,
    sentVotes1Correct,
    sentVotes0Faulty,
    sentVotes1Faulty,
    received0,
    received1,
    decision,
    terminated

vars == <<proposal, hasSent, sentVotes0Correct, sentVotes1Correct, 
          sentVotes0Faulty, sentVotes1Faulty, received0, received1, 
          decision, terminated>>

TypeOK ==
    /\ proposal \in [CorrectProcs -> {0, 1}]
    /\ hasSent \in [CorrectProcs -> BOOLEAN]
    /\ sentVotes0Correct \in 0..N
    /\ sentVotes1Correct \in 0..N
    /\ sentVotes0Faulty \in 0..N
    /\ sentVotes1Faulty \in 0..N
    /\ received0 \in [CorrectProcs -> 0..N]
    /\ received1 \in [CorrectProcs -> 0..N]
    /\ decision \in [CorrectProcs -> {-1, 0, 1, 2}]
    /\ terminated \in [CorrectProcs -> BOOLEAN]
    /\ sentVotes0Correct + sentVotes1Correct <= N - F
    /\ sentVotes0Faulty <= F
    /\ sentVotes1Faulty <= F

Init ==
    /\ proposal \in [CorrectProcs -> {0, 1}]
    /\ hasSent = [p \in CorrectProcs |-> FALSE]
    /\ sentVotes0Correct = 0
    /\ sentVotes1Correct = 0
    /\ sentVotes0Faulty = 0
    /\ sentVotes1Faulty = 0
    /\ received0 = [p \in CorrectProcs |-> 0]
    /\ received1 = [p \in CorrectProcs |-> 0]
    /\ decision = [p \in CorrectProcs |-> -1]
    /\ terminated = [p \in CorrectProcs |-> FALSE]

Send(p) ==
    /\ p \in CorrectProcs
    /\ ~hasSent[p]
    /\ hasSent' = [hasSent EXCEPT ![p] = TRUE]
    /\ IF proposal[p] = 0
       THEN /\ sentVotes0Correct' = sentVotes0Correct + 1
            /\ UNCHANGED sentVotes1Correct
       ELSE /\ sentVotes1Correct' = sentVotes1Correct + 1
            /\ UNCHANGED sentVotes0Correct
    /\ UNCHANGED <<proposal, sentVotes0Faulty, sentVotes1Faulty, 
                   received0, received1, decision, terminated>>

ByzantineSend0 ==
    /\ sentVotes0Faulty < F
    /\ sentVotes0Faulty' = sentVotes0Faulty + 1
    /\ UNCHANGED <<proposal, hasSent, sentVotes0Correct, sentVotes1Correct,
                   sentVotes1Faulty, received0, received1, decision, terminated>>

ByzantineSend1 ==
    /\ sentVotes1Faulty < F
    /\ sentVotes1Faulty' = sentVotes1Faulty + 1
    /\ UNCHANGED <<proposal, hasSent, sentVotes0Correct, sentVotes1Correct,
                   sentVotes0Faulty, received0, received1, decision, terminated>>

TotalSent0 == sentVotes0Correct + sentVotes0Faulty
TotalSent1 == sentVotes1Correct + sentVotes1Faulty

Receive0(p) ==
    /\ p \in CorrectProcs
    /\ ~terminated[p]
    /\ received0[p] < TotalSent0
    /\ received0' = [received0 EXCEPT ![p] = received0[p] + 1]
    /\ UNCHANGED <<proposal, hasSent, sentVotes0Correct, sentVotes1Correct,
                   sentVotes0Faulty, sentVotes1Faulty, received1, decision, terminated>>

Receive1(p) ==
    /\ p \in CorrectProcs
    /\ ~terminated[p]
    /\ received1[p] < TotalSent1
    /\ received1' = [received1 EXCEPT ![p] = received1[p] + 1]
    /\ UNCHANGED <<proposal, hasSent, sentVotes0Correct, sentVotes1Correct,
                   sentVotes0Faulty, sentVotes1Faulty, received0, decision, terminated>>

TotalReceived(p) == received0[p] + received1[p]

Decide(p) ==
    /\ p \in CorrectProcs
    /\ ~terminated[p]
    /\ decision[p] = -1
    /\ TotalReceived(p) >= N - T
    /\ \/ /\ received0[p] >= N - T
          /\ decision' = [decision EXCEPT ![p] = 0]
       \/ /\ received1[p] >= N - T
          /\ decision' = [decision EXCEPT ![p] = 1]
       \/ /\ received0[p] < N - T
          /\ received1[p] < N - T
          /\ decision' = [decision EXCEPT ![p] = 2]
    /\ terminated' = [terminated EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<proposal, hasSent, sentVotes0Correct, sentVotes1Correct,
                   sentVotes0Faulty, sentVotes1Faulty, received0, received1>>

Next ==
    \/ \E p \in CorrectProcs : Send(p)
    \/ ByzantineSend0
    \/ ByzantineSend1
    \/ \E p \in CorrectProcs : Receive0(p)
    \/ \E p \in CorrectProcs : Receive1(p)
    \/ \E p \in CorrectProcs : Decide(p)

Fairness ==
    /\ \A p \in CorrectProcs : WF_vars(Send(p))
    /\ \A p \in CorrectProcs : WF_vars(Receive0(p))
    /\ \A p \in CorrectProcs : WF_vars(Receive1(p))
    /\ \A p \in CorrectProcs : WF_vars(Decide(p))

Spec == Init /\ [][Next]_vars /\ Fairness

AllProposeZero == \A p \in CorrectProcs : proposal[p] = 0
AllProposeOne == \A p \in CorrectProcs : proposal[p] = 1

NoCorrectDecidesOne == \A p \in CorrectProcs : decision[p] # 1
NoCorrectDecidesZero == \A p \in CorrectProcs : decision[p] # 0

SafetyZero == AllProposeZero => []NoCorrectDecidesOne
SafetyOne == AllProposeOne => []NoCorrectDecidesZero

OneStep0_Ltl == [](AllProposeZero => []NoCorrectDecidesOne)
OneStep1_Ltl == [](AllProposeOne => []NoCorrectDecidesZero)

AllDecideOne ==
    \A p \in CorrectProcs : 
        (AllProposeOne => <>(terminated[p] /\ decision[p] \in {1, 2}))

BoundInvariant ==
    /\ sentVotes0Faulty <= F
    /\ sentVotes1Faulty <= F
    /\ \A p \in CorrectProcs : received0[p] <= N
    /\ \A p \in CorrectProcs : received1[p] <= N
    /\ \A p \in CorrectProcs : received0[p] >= 0
    /\ \A p \in CorrectProcs : received1[p] >= 0

=============================================================================