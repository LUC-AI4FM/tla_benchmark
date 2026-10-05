---------------------------- MODULE ByzantineConsensus ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F, Procs

ASSUME NGreater3T == N > 3 * T
ASSUME TGeqF == T >= F
ASSUME FGeq0 == F >= 0
ASSUME ProcsSize == Cardinality(Procs) = N

VARIABLES
    isByzantine,
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

vars == <<isByzantine, proposal, hasSent, sentVotes0Correct, sentVotes1Correct,
          sentVotes0Faulty, sentVotes1Faulty, received0, received1, decision, terminated>>

CorrectProcs == {p \in Procs : ~isByzantine[p]}
ByzantineProcs == {p \in Procs : isByzantine[p]}

TypeOK ==
    /\ isByzantine \in [Procs -> BOOLEAN]
    /\ proposal \in [Procs -> {0, 1}]
    /\ hasSent \in [Procs -> BOOLEAN]
    /\ sentVotes0Correct \in 0..N
    /\ sentVotes1Correct \in 0..N
    /\ sentVotes0Faulty \in 0..N
    /\ sentVotes1Faulty \in 0..N
    /\ received0 \in [Procs -> 0..N]
    /\ received1 \in [Procs -> 0..N]
    /\ decision \in [Procs -> {-1, 0, 1, 2}]
    /\ terminated \in [Procs -> BOOLEAN]

Init ==
    /\ isByzantine \in [Procs -> BOOLEAN]
    /\ Cardinality({p \in Procs : isByzantine[p]}) <= F
    /\ proposal \in [Procs -> {0, 1}]
    /\ hasSent = [p \in Procs |-> FALSE]
    /\ sentVotes0Correct = 0
    /\ sentVotes1Correct = 0
    /\ sentVotes0Faulty = 0
    /\ sentVotes1Faulty = 0
    /\ received0 = [p \in Procs |-> 0]
    /\ received1 = [p \in Procs |-> 0]
    /\ decision = [p \in Procs |-> -1]
    /\ terminated = [p \in Procs |-> FALSE]

SendVoteCorrect(p) ==
    /\ ~isByzantine[p]
    /\ ~hasSent[p]
    /\ hasSent' = [hasSent EXCEPT ![p] = TRUE]
    /\ IF proposal[p] = 0
       THEN /\ sentVotes0Correct' = sentVotes0Correct + 1
            /\ UNCHANGED sentVotes1Correct
       ELSE /\ sentVotes1Correct' = sentVotes1Correct + 1
            /\ UNCHANGED sentVotes0Correct
    /\ UNCHANGED <<isByzantine, proposal, sentVotes0Faulty, sentVotes1Faulty,
                   received0, received1, decision, terminated>>

SendVoteByzantine(p) ==
    /\ isByzantine[p]
    /\ ~hasSent[p]
    /\ hasSent' = [hasSent EXCEPT ![p] = TRUE]
    /\ \E v \in {0, 1} :
        IF v = 0
        THEN /\ sentVotes0Faulty' = sentVotes0Faulty + 1
             /\ UNCHANGED sentVotes1Faulty
        ELSE /\ sentVotes1Faulty' = sentVotes1Faulty + 1
             /\ UNCHANGED sentVotes0Faulty
    /\ UNCHANGED <<isByzantine, proposal, sentVotes0Correct, sentVotes1Correct,
                   received0, received1, decision, terminated>>

TotalSent0 == sentVotes0Correct + sentVotes0Faulty
TotalSent1 == sentVotes1Correct + sentVotes1Faulty

ReceiveVote(p) ==
    /\ ~terminated[p]
    /\ received0[p] + received1[p] < N
    /\ \/ /\ received0[p] < TotalSent0
          /\ received0' = [received0 EXCEPT ![p] = received0[p] + 1]
          /\ UNCHANGED received1
       \/ /\ received1[p] < TotalSent1
          /\ received1' = [received1 EXCEPT ![p] = received1[p] + 1]
          /\ UNCHANGED received0
    /\ UNCHANGED <<isByzantine, proposal, hasSent, sentVotes0Correct, sentVotes1Correct,
                   sentVotes0Faulty, sentVotes1Faulty, decision, terminated>>

TotalReceived(p) == received0[p] + received1[p]

Decide(p) ==
    /\ ~isByzantine[p]
    /\ ~terminated[p]
    /\ TotalReceived(p) >= N - T
    /\ \/ /\ received0[p] >= N - T
          /\ decision' = [decision EXCEPT ![p] = 0]
       \/ /\ received1[p] >= N - T
          /\ decision' = [decision EXCEPT ![p] = 1]
       \/ /\ received0[p] < N - T
          /\ received1[p] < N - T
          /\ decision' = [decision EXCEPT ![p] = 2]
    /\ terminated' = [terminated EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<isByzantine, proposal, hasSent, sentVotes0Correct, sentVotes1Correct,
                   sentVotes0Faulty, sentVotes1Faulty, received0, received1>>

Next ==
    \/ \E p \in Procs : SendVoteCorrect(p)
    \/ \E p \in Procs : SendVoteByzantine(p)
    \/ \E p \in Procs : ReceiveVote(p)
    \/ \E p \in Procs : Decide(p)

Fairness ==
    /\ \A p \in Procs : WF_vars(SendVoteCorrect(p))
    /\ \A p \in Procs : WF_vars(ReceiveVote(p))
    /\ \A p \in Procs : WF_vars(Decide(p))

Spec == Init /\ [][Next]_vars /\ Fairness

ByzantineBound ==
    Cardinality({p \in Procs : isByzantine[p]}) <= F

CountBounds ==
    /\ sentVotes0Correct \in 0..N
    /\ sentVotes1Correct \in 0..N
    /\ sentVotes0Faulty \in 0..N
    /\ sentVotes1Faulty \in 0..N
    /\ \A p \in Procs : received0[p] \in 0..N
    /\ \A p \in Procs : received1[p] \in 0..N

AllCorrectPropose0 == \A p \in Procs : ~isByzantine[p] => proposal[p] = 0
AllCorrectPropose1 == \A p \in Procs : ~isByzantine[p] => proposal[p] = 1

SafetyValidity0 ==
    AllCorrectPropose0 => \A p \in Procs : (~isByzantine[p] => decision[p] # 1)

SafetyValidity1 ==
    AllCorrectPropose1 => \A p \in Procs : (~isByzantine[p] => decision[p] # 0)

Safety == SafetyValidity0 /\ SafetyValidity1

LivenessTermination ==
    \A p \in Procs : ~isByzantine[p] => <>(terminated[p])

Liveness == LivenessTermination

Invariants == TypeOK /\ ByzantineBound /\ CountBounds /\ Safety

===================================================================================