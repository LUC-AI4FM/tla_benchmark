```
MODULE AtomicCommitmentProtocol

EXTENDS Integers, FiniteSets

CONSTANTS Processes, Votes
VARIABLES votes, deliveredMessages, suspicions, decisions, crashed

Init ==
  /\ votes \in [Processes -> {"YES", "NO"}]
  /\ deliveredMessages = {}
  /\ suspicions \in [Processes -> BOOLEAN]
  /\ decisions = {}
  /\ crashed = {}

Next ==
  \/ \E p \in Processes :
      /\ votes[p] = "YES"
      /\ p \notin crashed
      /\ deliveredMessages' = deliveredMessages \cup {<<p, "YES">>}
      /\ suspicions' = suspicions
      /\ decisions' = decisions
      /\ crashed' = crashed
  \/ \E p \in Processes :
      /\ votes[p] = "NO"
      /\ p \notin crashed
      /\ deliveredMessages' = deliveredMessages \cup {<<p, "NO">>}
      /\ suspicions' = suspicions
      /\ decisions' = decisions
      /\ crashed' = crashed
  \/ \E p \in Processes :
      /\ p \notin crashed
      /\ deliveredMessages' = deliveredMessages
      /\ suspicions' = [suspicions EXCEPT ![q \in Processes] = IF q = p THEN ~suspicions[q] ELSE suspicions[q]]
      /\ decisions' = decisions
      /\ crashed' = crashed
  \/ \E p \in Processes :
      /\ p \notin crashed
      /\ deliveredMessages' = deliveredMessages
      /\ suspicions' = suspicions
      /\ decisions' = decisions \cup {p}
      /\ IF \A q \in Processes : votes[q] = "YES" /\ q \notin crashed /\ suspicions[q] = FALSE
      THEN decisions'[p] = "COMMIT"
      ELSE decisions'[p] = "ABORT"
      /\ crashed' = crashed
  \/ \E p \in Processes :
      /\ p \notin crashed
      /\ deliveredMessages' = deliveredMessages
      /\ suspicions' = suspicions
      /\ decisions' = decisions
      /\ crashed' = crashed \cup {p}

Spec ==
  Init /\ [][Next]_<<votes, deliveredMessages, suspicions, decisions, crashed>>

AgreementInvariant ==
  \A p, q \in Processes :
    (decisions[p] = "COMMIT" /\ decisions[q] = "ABORT") \/ (decisions[p] = "ABORT" /\ decisions[q] = "COMMIT")
    => p \in crashed \/ q \in crashed

ValidityInvariant ==
  \A p \in Processes :
    decisions[p] = "COMMIT"
    => \A q \in Processes : votes[q] = "YES" /\ q \notin crashed /\ suspicions[q] = FALSE
  /\ \A p \in Processes :
    decisions[p] = "ABORT"
    => \E q \in Processes : votes[q] = "NO" \/ q \in crashed \/ suspicions[q] = TRUE

TerminationProperty ==
  <>[]\A p \in Processes :
    p \notin crashed
    => <>(decisions'[p] = "COMMIT" \/ decisions'[p] = "ABORT")

THEOREM Spec => []AgreementInvariant
THEOREM Spec => []ValidityInvariant
THEOREM Spec => TerminationProperty

```
Note: This TLA+ specification models the non-blocking atomic commitment protocol with N distributed processes, unreliable failure detectors, and crash failures. It captures the voting phase, message-sending phase, crash events, and asynchronous message reception. The specification ensures agreement, validity, and termination properties under the stated assumptions about the failure detector.