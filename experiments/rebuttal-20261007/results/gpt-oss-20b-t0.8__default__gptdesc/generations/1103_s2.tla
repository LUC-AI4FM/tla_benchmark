MODULE NBAC
EXTENDS Naturals, Sequences, TLC, SETS

CONSTANT N

VARIABLES votes, sent, seenVotes, msgBuffer, crashed, fd, dec

Proc == 1..N
VoteVal == {"YES","NO"}
Decision == {"COMMIT","ABORT"}
MsgType == {"VOTE","DECIDE"}
UNDEF == "UNDEF"

vars == << votes, sent, seenVotes, msgBuffer, crashed, fd, dec >>

Init ==
  /\ votes = [p \in Proc |-> CHOOSE v \in VoteVal : v]
  /\ sent = [p \in Proc |-> FALSE]
  /\ seenVotes = [p \in Proc |-> {}]
  /\ msgBuffer = [p \in Proc |-> {}]
  /\ crashed = [p \in Proc |-> FALSE]
  /\ fd = [p \in Proc |-> {}]
  /\ dec = UNDEF

SendVote(p) ==
  /\ ¬crashed[p]
  /\ ¬sent[p]
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ msgBuffer' =
       [msgBuffer EXCEPT
           ![q] =
              IF q ≠ p /\ ¬crashed[q]
                 THEN msgBuffer[q] ∪ { [type |-> "VOTE", sender |-> p, payload |-> votes[p]] }
                 ELSE msgBuffer[q]]
  /\ UNCHANGED << seenVotes, crashed, fd, dec >>

ReceiveMsg(p) ==
  /\ ¬crashed[p]
  /\ msgBuffer[p] ≠ {}
  /\ LET m == CHOOSE m \in msgBuffer[p] : TRUE IN
       /\ IF m.type = "VOTE"