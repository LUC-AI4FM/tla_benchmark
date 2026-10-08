\* NBAC.tla -- non‑blocking atomic commitment with crash failures
\*
\* This module encodes a simplified NBAC algorithm following Raynal 1997.
\* Processes vote YES or NO, exchange VOTE messages, may crash,
\* and maintain a local failure detector (FD) that nondeterministically reports crashes.

MODULE NBAC
EXTENDS Naturals, Sequences, TLC

CONSTANT N

Process == 1 .. N

VoteVal          == {"YES", "NO", "UNDECIDED"}
DecisionVal      == {"COMMITTED", "ABORTED", "UNKNOWN"}
MessageType      == {"VOTE"}
Message          == [sender : Process, mtype : MessageType, vote : VoteVal]

VARIABLES vote, decisions, crashed, fd, inbox

vars == <<vote, decisions, crashed, fd, inbox>>

Init ==
  /\ vote = [p ∈ Process |-> "UNDECIDED"]
  /\ decisions = [p ∈ Process |-> "UNKNOWN"]
  /\ crashed = [p ∈ Process |-> FALSE]
  /\ fd = [p ∈ Process |-> {}]
