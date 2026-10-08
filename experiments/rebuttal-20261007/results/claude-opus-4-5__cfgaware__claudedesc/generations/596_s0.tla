---- MODULE DistributedTransactionMC ----

EXTENDS DistributedTransaction

CONSTANTS k1, k2, c1, c2

MCKey == {k1, k2}

MCPessimisticClient == {c1}

MCOptimisticClient == {c2}

MCClientKey == [c1 |-> {k1, k2}, c2 |-> {k1, k2}]

MCClientReadKey == [c1 |-> {}, c2 |-> {k1, k2}]

MCClientWriteKey == [c1 |-> {k1, k2}, c2 |-> {k1, k2}]

MCClientPrimaryKey == [c1 |-> k1, c2 |-> k1]

====