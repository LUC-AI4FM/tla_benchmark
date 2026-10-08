--------------------------- MODULE OneStepConsensus ---------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F
ASSUME N > 3 * T ∧ T >= F

VARIABLES correctProposals, 
          sentVotesCorrect, 
          sentVotesFaulty, 
          receivedVotes,
          decisions,
          undecided

TypeOK == 
  /\ correctProposals \in [1..N -> {0, 1}]
  /\ sentVotesCorrect \in [1..N -> Nat]
  /\ sentVotesFaulty \in [1..N -> Nat]
  /\ receivedVotes \in [1..N -> (Nat -> Nat)]
  /\ decisions \in [1..N -> ({0, 1} \cup {<<"undecided">>})]
  /\ undecided \in [1..N -> Bool]

OneStep0_Ltl == 
  <>[]<>(\E p \in 1..N : decisions[p] = 1)

OneStep1_Ltl == 
  <>[]<>(\E p \in 1..N : decisions[p] = 0)

AllDecideOne == 
  []<>(\A p \in 1..N : decisions[p] \in {0, 1})

Spec == 
  /\ TypeOK
  /\ [][TypeOK'_]
  /\ WF_(p \in 1..N)_(decide(p))
  /\ OneStep0_Ltl
  /\ OneStep1_Ltl

Init == 
  /\ correctProposals = [i \in 1..N |-> CHOOSE v \in {0, 1} : TRUE]
  /\ sentVotesCorrect = [i \in 1..N |-> 0]
  /\ sentVotesFaulty = [i \in 1..N |-> 0]
  /\ receivedVotes = [i \in 1..N |-> [v \in {0, 1} |-> 0]]
  /\ decisions = [i \in 1..N |-> <<"undecided">>]
  /\ undecided = [i \in 1..N |-> TRUE]

Next == 
  (\E p \in 1..N : 
    /\ correctProposals[p] = 0
    /\ sentVotesCorrect[p] = 0
    /\ sentVotesFaulty[p] = 0
    /\ receivedVotes[p][0] < N - T
    /\ receivedVotes[p][1] < N - T
    /\ undecided[p]
    /\ decisions' = [decisions EXCEPT ![p] = IF receivedVotes[p][0] >= N - T THEN 0 ELSE IF receivedVotes[p][1] >= N - T THEN 1 ELSE <<"undecided">>]
    /\ sentVotesCorrect' = [sentVotesCorrect EXCEPT ![p] = sentVotesCorrect[p] + 1]
    /\ sentVotesFaulty' = sentVotesFaulty
    /\ receivedVotes' = [receivedVotes EXCEPT ![p] = [receivedVotes[p] EXCEPT ![0] = receivedVotes[p][0] + 1]]
    /\ undecided' = [undecided EXCEPT ![p] = IF decisions'[p] = <<"undecided">> THEN TRUE ELSE FALSE]
  )
  \/ 
  (\E p \in 1..N : 
    /\ correctProposals[p] = 1
    /\ sentVotesCorrect[p] = 0
    /\ sentVotesFaulty[p] = 0
    /\ receivedVotes[p][0] < N - T
    /\ receivedVotes[p][1] < N - T
    /\ undecided[p]
    /\ decisions' = [decisions EXCEPT ![p] = IF receivedVotes[p][0] >= N - T THEN 0 ELSE IF receivedVotes[p][1] >= N - T THEN 1 ELSE <<"undecided">>]
    /\ sentVotesCorrect' = [sentVotesCorrect EXCEPT ![p] = sentVotesCorrect[p] + 1]
    /\ sentVotesFaulty' = sentVotesFaulty
    /\ receivedVotes' = [receivedVotes EXCEPT ![p] = [receivedVotes[p] EXCEPT ![1] = receivedVotes[p][1] + 1]]
    /\ undecided' = [undecided EXCEPT ![p] = IF decisions'[p] = <<"undecided">> THEN TRUE ELSE FALSE]
  )
  \/ 
  (\E p \in 1..N, q \in 1..N : 
    /\ correctProposals[p] = 0
    /\ sentVotesCorrect[q] > 0
    /\ receivedVotes[p][0] < N - T
    /\ undecided[p]
    /\ decisions' = decisions
    /\ sentVotesCorrect' = sentVotesCorrect
    /\ sentVotesFaulty' = sentVotesFaulty
    /\ receivedVotes' = [receivedVotes EXCEPT ![p] = [receivedVotes[p] EXCEPT ![0] = receivedVotes[p][0] + 1]]
    /\ undecided' = undecided
  )
  \/ 
  (\E p \in 1..N, q \in 1..N : 
    /\ correctProposals[p] = 1
    /\ sentVotesCorrect[q] > 0
    /\ receivedVotes[p][1] < N - T
    /\ undecided[p]
    /\ decisions' = decisions
    /\ sentVotesCorrect' = sentVotesCorrect
    /\ sentVotesFaulty' = sentVotesFaulty
    /\ receivedVotes' = [receivedVotes EXCEPT ![p] = [receivedVotes[p] EXCEPT ![1] = receivedVotes[p][1] + 1]]
    /\ undecided' = undecided
  )

THEOREM Spec => []TypeOK
THEOREM Spec => OneStep0_Ltl
THEOREM Spec => OneStep1_Ltl
THEOREM Spec => AllDecideOne

=============================================================================