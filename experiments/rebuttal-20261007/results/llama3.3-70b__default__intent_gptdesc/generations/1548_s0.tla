```
MODULE OneStepByzantineConsensus
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F
ASSUME N > 3 * T ∧ T >= F

VARIABLES correctProposals,
          sentVotesCorrect,
          sentVotesFaulty,
          receivedVotes,
          decisions,
          undecidedProcesses

Init ==
  ∧ correctProposals \in [1..N → {0, 1}]
  ∧ sentVotesCorrect = [i \in 1..N |-> 0]
  ∧ sentVotesFaulty = [i \in 1..N |-> 0]
  ∧ receivedVotes = [i \in 1..N |-> {}]
  ∧ decisions = [i \in 1..N |-> ⊥]
  ∧ undecidedProcesses = {}

Next ==
  ∨ (∃ i \in 1..N :
      ∧ sentVotesCorrect[i] = 0
      ∧ sentVotesCorrect' = [sentVotesCorrect EXCEPT ![i] = 1]
      ∧ receivedVotes' = receivedVotes
      ∧ decisions' = decisions
      ∧ undecidedProcesses' = undecidedProcesses)
  ∨ (∃ i \in 1..N, v \in {0, 1} :
      ∧ sentVotesFaulty[i] = 0
      ∧ sentVotesFaulty' = [sentVotesFaulty EXCEPT ![i] = 1]
      ∧ receivedVotes' = receivedVotes
      ∧ decisions' = decisions
      ∧ undecidedProcesses' = undecidedProcesses)
  ∨ (∃ i \in 1..N, j \in 1..N, v \in {0, 1} :
      ∧ (j \in correctProposals ∧ sentVotesCorrect[j] = 1) ∨ (j \in Domain sentVotesFaulty ∧ sentVotesFaulty[j] = 1)
      ∧ receivedVotes[i]' = receivedVotes[i] ∪ {v}
      ∧ sentVotesCorrect' = sentVotesCorrect
      ∧ sentVotesFaulty' = sentVotesFaulty
      ∧ decisions' = decisions
      ∧ undecidedProcesses' = undecidedProcesses)
  ∨ (∃ i \in 1..N :
      ∧ Card(receivedVotes[i]) >= N - T
      ∧ (decisions[i] = 0 ∧ Card({v \in receivedVotes[i] | v = 0}) >= N - T)
        ∨ (decisions[i] = 1 ∧ Card({v \in receivedVotes[i] | v = 1}) >= N - T)
      ∧ decisions' = [decisions EXCEPT ![i] = decisions[i]]
      ∧ sentVotesCorrect' = sentVotesCorrect
      ∧ sentVotesFaulty' = sentVotesFaulty
      ∧ receivedVotes' = receivedVotes
      ∧ undecidedProcesses' = undecidedProcesses)
  ∨ (∃ i \in 1..N :
      ∧ Card(receivedVotes[i]) >= N - T
      ∧ Card({v \in receivedVotes[i] | v = 0}) < N - T
      ∧ Card({v \in receivedVotes[i] | v = 1}) < N - T
      ∧ undecidedProcesses' = undecidedProcesses ∪ {i}
      ∧ decisions' = decisions
      ∧ sentVotesCorrect' = sentVotesCorrect
      ∧ sentVotesFaulty' = sentVotesFaulty
      ∧ receivedVotes' = receivedVotes)

Spec ==
  Init ∧ [][Next]_correctProposals, sentVotesCorrect, sentVotesFaulty, receivedVotes, decisions, undecidedProcesses

THEOREM Spec => []∀ i \in 1..N :
  (∀ j \in 1..N : correctProposals[j] = 0) ⇒ (decisions[i] ≠ 1)
  ∧ (∀ j \in 1..N : correctProposals[j] = 1) ⇒ (decisions[i] ≠ 0)

THEOREM Spec => WF_([Next]_correctProposals, sentVotesCorrect, sentVotesFaulty, receivedVotes, decisions, undecidedProcesses) =>
  []∃ i \in 1..N : decisions[i] ∈ {0, 1} ∨ i \in undecidedProcesses

THEOREM Spec => []Card(Domain sentVotesFaulty) <= F
THEOREM Spec => []∀ i \in 1..N :
  ∧ sentVotesCorrect[i] \in 0..1
  ∧ sentVotesFaulty[i] \in 0..1
  ∧ Card(receivedVotes[i]) <= N
```