---------------------------- MODULE MC_DistributedTransaction ----------------------------
(***************************************************************************)
(* Model-checking configuration for the DistributedTransaction module.     *)
(* Declares two keys and three clients, and defines the optimistic and     *)
(* pessimistic client sets, the read and write key sets of each client,    *)
(* and the primary key of each client.                                     *)
(*                                                                         *)
(* The module is self-contained so that SANY can parse it on its own. It   *)
(* has a trivial Init/Next/Spec, plus invariants that check the            *)
(* configuration is well-formed.                                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

\* Model values for keys
CONSTANTS k1, k2

\* Model values for clients
CONSTANTS c1, c2, c3

-----------------------------------------------------------------------------
\* Configuration layer (parameters for DistributedTransaction)

MC_KEY == {k1, k2}

MC_OPTIMISTIC_CLIENT == {c1}

MC_PESSIMISTIC_CLIENT == {c2, c3}

MC_CLIENT == MC_OPTIMISTIC_CLIENT \cup MC_PESSIMISTIC_CLIENT

\* Keys that each client may read
MC_CLIENT_READ_KEY == [c \in MC_CLIENT |->
                         IF c = c1 THEN {}
                         ELSE IF c = c2 THEN {k1}
                         ELSE {k2}]

\* Keys that each client may write
MC_CLIENT_WRITE_KEY == [c \in MC_CLIENT |->
                          IF c = c1 THEN {k1, k2}
                          ELSE IF c = c2 THEN {k2}
                          ELSE {k1}]

\* Keys touched by each client
MC_CLIENT_KEY == [c \in MC_CLIENT |->
                    MC_CLIENT_READ_KEY[c] \cup MC_CLIENT_WRITE_KEY[c]]

\* Primary key of each client
MC_CLIENT_PRIMARY == [c \in MC_CLIENT |->
                        IF c = c1 THEN k1
                        ELSE IF c = c2 THEN k2
                        ELSE k1]

-----------------------------------------------------------------------------
\* Trivial behavior. The configuration itself defines no actions.

VARIABLE config

vars == <<config>>

ConfigRecord == [ keys       |-> MC_KEY,
                  optimistic  |-> MC_OPTIMISTIC_CLIENT,
                  pessimistic |-> MC_PESSIMISTIC_CLIENT,
                  readKeys    |-> MC_CLIENT_READ_KEY,
                  writeKeys   |-> MC_CLIENT_WRITE_KEY,
                  primary     |-> MC_CLIENT_PRIMARY ]

Init == config = ConfigRecord

Next == UNCHANGED config

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Well-formedness invariants of the configuration

TypeOK ==
    /\ config = ConfigRecord
    /\ MC_CLIENT_READ_KEY  \in [MC_CLIENT -> SUBSET MC_KEY]
    /\ MC_CLIENT_WRITE_KEY \in [MC_CLIENT -> SUBSET MC_KEY]
    /\ MC_CLIENT_PRIMARY   \in [MC_CLIENT -> MC_KEY]

\* A client is either optimistic or pessimistic, never both
ClientPartition ==
    MC_OPTIMISTIC_CLIENT \cap MC_PESSIMISTIC_CLIENT = {}

\* Each client's primary key is one of the keys it writes
PrimaryIsWritten ==
    \A c \in MC_CLIENT : MC_CLIENT_PRIMARY[c] \in MC_CLIENT_WRITE_KEY[c]

\* Every client writes at least one key
NonEmptyWrites ==
    \A c \in MC_CLIENT : MC_CLIENT_WRITE_KEY[c] # {}

ConfigInvariant ==
    /\ TypeOK
    /\ ClientPartition
    /\ PrimaryIsWritten
    /\ NonEmptyWrites

THEOREM Spec => []ConfigInvariant
=============================================================================