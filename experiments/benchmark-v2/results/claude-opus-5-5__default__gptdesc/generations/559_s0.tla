---------------------------- MODULE MCPaxosCommit ----------------------------
EXTENDS PaxosCommit

TCommitSpec == INSTANCE TCommit

TCommitSpecProperty == TCommitSpec!TCSpec

THEOREM PCSpec => TCommitSpecProperty
=============================================================================