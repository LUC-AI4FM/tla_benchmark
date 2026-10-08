------------------------------ MODULE MCSpecMultiNodeReadsAlt ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS
  Nodes, Clients, Views, MaxSeq,
  PreCommittedTxs

\* ------------------------------------------------------------------
\* Types
\* ------------------------------------------------------------------
TxId == [view:Views, seq:Nat]
Transaction == [id:TxId, client:Clients, observed: SET OF TxId]

ASSUME PreCommittedTxs \in SUBSET Transaction

\* ------------------------------------------------------------------
\* Variables
\* ------------------------------------------------------------------
VARIABLES
  ledgerBranches,
  pending,
  committed,
  status

\* ------------------------------------------------------------------
\* Type invariant
\* ------------------------------------------------------------------
TypeInvariant ==
  /\ ledgerBranches \in [view \in Views -> SUBSET TxId]
  /\ pending \in [client \in Clients -> SUBSET Transaction]
  /\ committed \in SUBSET Transaction
  /\ status \in [txid \in TxId -> {"Pending","Committed"}]

\* ------------------------------------------------------------------
\* Helper functions
\* ------------------------------------------------------------------
NextSeq(v) ==
  LET seqs == { t.id.seq : t \in committed /\ t.id.view = v }
      n    == CHOOSE n \in Nat : n > 0 /\ n <= MaxSeq /\ n \notin seqs
  IN n

NextTxId(v) ==
  [view |-> v, seq |-> NextSeq(v)]

PriorCommitted(view, seq) ==
  { t.id : t \in committed /\ t.id.view = view /\ t.id.seq < seq }

AllTxIds == { t.id : t \in PreCommittedTxs }

\* ------------------------------------------------------------------
\* Initial state
\* ------------------------------------------------------------------
Init ==
  /\ ledgerBranches = [v \in Views |-> {}]
  /\ pending      = [c \in Clients |-> {}]
  /\ committed    = {}
  /\ status       = [t \in TxId :> "Pending"]

AltInit ==
  /\ ledgerBranches = [v \in Views |
        LET ids == { t.id : t \in PreCommittedTxs /\ t.id.view = v }
        IN ids ]
  /\ pending      = [c \in Clients |-> {}]
  /\ committed    = PreCommittedTxs
  /\ status       = [t \in TxId :
        IF t \in AllTxIds THEN "Committed" ELSE "Pending"]

\* ------------------------------------------------------------------
\* Actions
\* ------------------------------------------------------------------
SubmitTx ==
  /\ client \in Clients
  /\ v \in Views
  /\ txId == NextTxId(v)
  /\ tx   == [id |-> txId, client |-> client, observed |-> {}]
  /\ tx \notin pending[client]
  /\ pending' = [pending EXCEPT ![client] = @ UNION {tx}]
  /\ UNCHANGED <<ledgerBranches, committed, status>>

RespondTx ==
  /\ client \in Clients
  /\ tx \in pending[client]
  /\ observed == PriorCommitted(tx.id.view, tx.id.seq)
  /\ tx'   == [tx EXCEPT !.observed = observed]
  /\ pending'    = [pending EXCEPT ![client] = @ \ {tx}]
  /\ committed'  = committed UNION {tx'}
  /\ status'     = [status EXCEPT ![tx.id] = "Committed"]
  /\ ledgerBranches' =
        [ledgerBranches EXCEPT ![tx.id.view] = @ UNION {tx.id}]

Fork ==
  /\ v1 \in Views
  /\ v2 \in Views
  /\ v1 # v2
  /\ seq \in { t.id.seq : t \in committed /\ t.id.view = v1 }
  /\ ledgerBranches' =
        [ledgerBranches EXCEPT ![v2] = @ UNION
           { t.id : t \in committed /\ t.id.view = v1 /\ t.id.seq <= seq }]
  /\ UNCHANGED <<pending, committed, status>>

Next ==
  \/ SubmitTx
  \/ RespondTx
  \/ Fork

\* ------------------------------------------------------------------
\* Specification
\* ------------------------------------------------------------------
Spec == Init /\ TypeInvariant /\ [][Next]_<<ledgerBranches, pending, committed, status>>
AltSpec == AltInit /\ TypeInvariant /\ [][Next]_<<ledgerBranches, pending, committed, status>>

=============================================================================