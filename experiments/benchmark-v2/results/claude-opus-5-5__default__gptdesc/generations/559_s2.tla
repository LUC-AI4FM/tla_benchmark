------------------------------ MODULE MCPaxosCommit ------------------------------
EXTENDS PaxosCommit

\* The constants (RM, Acceptor, Majority, Ballot) and the variables
\* (rmState, aState, msgs) come from module PaxosCommit.

Init == PCInit

Next == PCNext

Spec == PCSpec

TCommitSpec == INSTANCE TCommit

TCommitSpecProperty == TCommitSpec!TCSpec

THEOREM PCSpec => TCommitSpecProperty
==================================================================================