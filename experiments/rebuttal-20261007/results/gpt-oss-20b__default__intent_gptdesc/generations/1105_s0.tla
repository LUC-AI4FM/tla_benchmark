MODULE AtomicCommit
EXTENDS Naturals

CONSTANT N
CONSTANT VotesDist \in [1..N -> {"YES","NO"}]

Proc == 1 .. N
VoteSet == {"YES", "NO"}
OutcomeSet == {"COMMIT", "ABORT"}
DecisionSet == {"none", "COMMIT", "ABORT"}

VARIABLES status, sentMsg, pending, recvVotes, decision

Init ==
  /\ status = [p \in Proc |-> "alive"]
  /\ sentMsg = [p \in Proc |-> "NONE"]
  /\ pending = [p \in Proc |-> {}]
  /\ recvVotes = [p \in Proc |-> {}]
  /\ decision = [p \in Proc |-> "none"]

Send ==
  \E p \in Proc :
    /\ status[p] = "alive"
    /\ sentMsg[p] = "