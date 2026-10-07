------------------------------ MODULE MultiNodeReadsBase ------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  NODES,       \* Non-empty set of node identifiers
  TX,          \* Set of transaction identifiers
  RESPVALUES   \* Set of possible read response values

VARIABLES
  ledger,      \* Function from NODES to a sequence of committed TXs (the branch per node)
  history      \* Sequence of history entries (responses and committed-status records)

vars == << ledger, history >>

(*
  History entries consist of either:
    - a Response entry: records a read response value for a tx at a node
    - a Committed entry: records that a tx is committed at a node
*)
ResponseEntry == [ type: {"Response"},  tx: TX, node: NODES, value: RESPVALUES ]
CommitEntry   == [ type: {"Committed"}, tx: TX, node: NODES, committed: BOOLEAN ]
HistoryEntry  == ResponseEntry \cup CommitEntry

IsResponse(e) == e.type = "Response"
IsCommittedEntry(e) == e.type = "Committed"

TypeOK ==
  /\ ledger \in [NODES -> Seq(TX)]
  /\ history \in Seq(HistoryEntry)

SeqToSet(s) == { s[i] : i \in 1..Len(s) }

Append(s, x) == s \o << x >>

Commit(n, t) ==
  /\ n \in NODES
  /\ t \in TX
  /\ t \notin SeqToSet(ledger[n])
  /\ ledger' = [ledger EXCEPT ![n] = Append(@, t)]
  /\ history' = Append(history, [type |-> "Committed", tx |-> t, node |-> n, committed |-> TRUE])

Read(n, t, v) ==
  /\ n \in NODES
  /\ t \in TX
  /\ v \in RESPVALUES
  /\ ledger' = ledger
  /\ history' = Append(history, [type |-> "Response", tx |-> t, node |-> n, value |-> v])

MCNextMultiNodeReadsAction ==
  ( \E n \in NODES, t \in TX: Commit(n, t))
  \/ ( \E n \in NODES, t \in TX, v \in RESPVALUES: Read(n, t, v))

InitBase ==
  /\ ledger \in [NODES -> Seq(TX)]
  /\ \A n \in NODES: ledger[n] = << >>
  /\ history = << >>

NextBase == MCNextMultiNodeReadsAction

SpecBase == InitBase /\ [][NextBase]_vars

=============================================================================