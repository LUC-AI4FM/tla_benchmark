------------------------------- MODULE ByzantineConsensus -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, CorrectProcs, FaultyProcs
ASSUME N > 3 * T /\ T >= F /\ (CorrectProcs \cup FaultyProcs) = {1..N} /\ Cardinality(FaultyProcs) <= F

VARIABLES sentVotesByCorrect, sentVotesByFaulty, receivedVotes

Init == 
    /\ sentVotesByCorrect = [p \in CorrectProcs |-> 0]
    /\ sentVotesByFaulty = [p \in FaultyProcs |-> 0]
    /\ receivedVotes = [p \in {1..N} |-> <<0, 0>>]

Next ==
    \/ \/ \E p \in CorrectProcs : 
            /\ sentVotesByCorrect[p] = 0
            /\ \E v \in {0, 1} :
                /\ sentVotesByCorrect' = [sentVotesByCorrect EXCEPT ![p] = 1]
                /\ sentVotesByFaulty' = sentVotesByFaulty
                /\ receivedVotes' = [receivedVotes EXCEPT ![p] = <<v, 0>>]
       \/ \E p \in FaultyProcs : 
            /\ sentVotesByFaulty[p] = 0
            /\ \E v \in {0, 1} :
                /\ sentVotesByCorrect' = sentVotesByCorrect
                /\ sentVotesByFaulty' = [sentVotesByFaulty EXCEPT ![p] = 1]
                /\ receivedVotes' = [receivedVotes EXCEPT ![p] = <<v, 0>>]
       \/ \E p \in {1..N} :
            /\ LET totalReceived == receivedVotes[p][1] + receivedVotes[p][2]
               IN
               /\ totalReceived < N - T
               /\ \E q \in {1..N}, v \in {0, 1} :
                   /\ sentVotesByCorrect[q] > 0 \/ sentVotesByFaulty[q] > 0
                   /\ receivedVotes' = [receivedVotes EXCEPT ![p][v+1] = receivedVotes[p][v+1] + 1]
       \/ \E p \in CorrectProcs :
            LET totalReceived == receivedVotes[p][1] + receivedVotes[p][2]
                votesFor0 == receivedVotes[p][1]
                votesFor1 == receivedVotes[p][2]
            IN
            /\ totalReceived >= N - T
            /\ (votesFor0 >= N - T \/ votesFor1 >= N - T)
            /\ sentVotesByCorrect' = sentVotesByCorrect
            /\ sentVotesByFaulty' = sentVotesByFaulty
            /\ receivedVotes' = [receivedVotes EXCEPT ![p] = <<IF votesFor0 >= N - T THEN 1 ELSE 0, IF votesFor1 >= N - T THEN 1 ELSE 0>>]

Spec ==
    /\ Init
    /\ [][Next]_<<sentVotesByCorrect, sentVotesByFaulty, receivedVotes>>
    /\ WF_next(<<sentVotesByCorrect, sentVotesByFaulty, receivedVotes>>)

SafetyProp ==
    \/ \A p \in CorrectProcs : 
        (/\ \A q \in CorrectProcs : receivedVotes[q][1] = N - T
         => receivedVotes[p][2] < N - T)
    \/ \A p \in CorrectProcs : 
        (/\ \A q \in CorrectProcs : receivedVotes[q][2] = N - T
         => receivedVotes[p][1] < N - T)

LivenessProp ==
    \A p \in CorrectProcs :
        WF_next(<<sentVotesByCorrect, sentVotesByFaulty, receivedVotes>>) ->
        <>[](receivedVotes[p][1] >= N - T \/ receivedVotes[p][2] >= N - T \/ (receivedVotes[p][1] + receivedVotes[p][2] >= N - T))

=============================================================================