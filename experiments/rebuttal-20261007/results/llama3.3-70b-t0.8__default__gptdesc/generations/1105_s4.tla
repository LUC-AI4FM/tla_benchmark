```
MODULE AsynchronousAtomicCommitment
EXTENDS Integers, Sequences, TLC

CONSTANTS ProcSet, QuorumSet
VARIABLES state, vote, suspected, sentMsgs, rcvdMsgs

Init ==
  /\ state \in [ProcSet -> {"initial", "voted", "aborted", "committed"}]
  /\ vote \in [ProcSet -> {"YES", "NO"}]
  /\ suspected \in [ProcSet -> BOOLEAN]
  /\ sentMsgs \in [ProcSet -> Seq(ProcSet)]
  /\ rcvdMsgs \in [ProcSet -> Seq(ProcSet)]
  /\ \A p \in ProcSet : state[p] = "initial"
  /\ (\A p \in ProcSet : vote[p] = "YES") \/ (\A p \in ProcSet : vote[p] = "NO")

TypeInvariant ==
  /\ state \in [ProcSet -> {"initial", "voted", "aborted", "committed"}]
  /\ vote \in [ProcSet -> {"YES", "NO"}]
  /\ suspected \in [ProcSet -> BOOLEAN]
  /\ sentMsgs \in [ProcSet -> Seq(ProcSet)]
  /\ rcvdMsgs \in [ProcSet -> Seq(ProcSet)]

Next ==
  \/ \E p \in ProcSet :
      /\ state[p] = "initial"
      /\ state' = [state EXCEPT ![p] = "voted"]
      /\ vote' = vote
      /\ suspected' = suspected
      /\ sentMsgs' = [sentMsgs EXCEPT ![p] = <<>>]
      /\ rcvdMsgs' = rcvdMsgs
  \/ \E p \in ProcSet :
      /\ state[p] = "voted"
      /\ vote[p] = "YES"
      /\ suspected' = [suspected EXCEPT ![p] = TRUE]
      /\ sentMsgs' = [sentMsgs EXCEPT ![p] = Append(sentMsgs[p], p)]
      /\ rcvdMsgs' = rcvdMsgs
      /\ state' = [state EXCEPT ![p] = "aborted"]
      /\ vote' = vote
  \/ \E p \in ProcSet :
      /\ state[p] = "voted"
      /\ vote[p] = "NO"
      /\ suspected' = [suspected EXCEPT ![p] = TRUE]
      /\ sentMsgs' = [sentMsgs EXCEPT ![p] = Append(sentMsgs[p], p)]
      /\ rcvdMsgs' = rcvdMsgs
      /\ state' = [state EXCEPT ![p] = "aborted"]
      /\ vote' = vote
  \/ \E p, q \in ProcSet :
      /\ state[p] = "voted"
      /\ state[q] = "initial"
      /\ suspected' = suspected
      /\ sentMsgs' = [sentMsgs EXCEPT ![q] = Append(sentMsgs[q], p)]
      /\ rcvdMsgs' = [rcvdMsgs EXCEPT ![p] = Append(rcvdMsgs[p], q)]
      /\ state' = [state EXCEPT ![q] = "voted"]
      /\ vote' = [vote EXCEPT ![q] = vote[p]]
  \/ \E p \in ProcSet :
      /\ state[p] = "aborted"
      /\ suspected' = suspected
      /\ sentMsgs' = sentMsgs
      /\ rcvdMsgs' = rcvdMsgs
      /\ state' = [state EXCEPT ![p] = "committed"]
      /\ vote' = vote

Agreement ==
  \A p, q \in ProcSet :
    (state[p] = "aborted") \/ (state[q] = "aborted") \/ (vote[p] = vote[q])

AbortValidity ==
  \A p \in ProcSet :
    state[p] = "aborted" => \E q \in ProcSet : vote[q] = "NO"

CommitValidity ==
  \A p \in ProcSet :
    state[p] = "committed" => \A q \in ProcSet : vote[q] = "YES"

Termination ==
  <>(\E p \in ProcSet : state[p] = "aborted") \/ <>(\E p \in ProcSet : state[p] = "committed")

EventualCommit ==
  []<>(\E p \in ProcSet : state[p] = "committed")

Spec ==
  /\ Init
  /\ [][Next]_state
  /\ WF_state(Next)
  /\ Agreement
  /\ AbortValidity
  /\ CommitValidity
  /\ Termination
  /\ EventualCommit
  /\ TypeInvariant

THEOREM Spec => [](Agreement /\ AbortValidity /\ CommitValidity /\ Termination /\ EventualCommit)

```
Note: The `WF_state(Next)` statement enforces weak fairness for non-stuttering process actions.