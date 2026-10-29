---------------------------- MODULE MC_DistributedTransaction ----------------------------
(***************************************************************************)
(* Small model-checking configuration for the DistributedTransaction       *)
(* system. It declares two keys and three clients, and defines:            *)
(*   - which clients are optimistic and which are pessimistic,             *)
(*   - which keys each client may read,                                    *)
(*   - which keys each client may write,                                   *)
(*   - the primary key of each client.                                     *)
(*                                                                         *)
(* This module only parameterizes the system. The trivial Init/Next/Spec   *)
(* below keep the configuration fixed so the module can be parsed and      *)
(* checked on its own. The configuration is meant to be substituted for    *)
(* the constants of the DistributedTransaction module.                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

\* Model values for keys and clients
CONSTANTS k1, k2
CONSTANTS c1, c2, c3

VARIABLES config

vars == << config >>

-----------------------------------------------------------------------------
(* Configuration definitions *)

MC_KEY == {k1, k2}

MC_CLIENT == {c1, c2, c3}

MC_OPTIMISTIC_CLIENT == {c1}

MC_PESSIMISTIC_CLIENT == {c2, c3}

MC_CLIENT_READ_KEY == [c \in MC_CLIENT |->
                         CASE c = c1 -> {}
                           [] c = c2 -> {k1, k2}
                           [] c = c3 -> {k1, k2}]

MC_CLIENT_WRITE_KEY == [c \in MC_CLIENT |->
                          CASE c = c1 -> {k1, k2}
                            [] c = c2 -> {k1}
                            [] c = c3 -> {k2}]

MC_CLIENT_KEY == [c \in MC_CLIENT |-> MC_CLIENT_READ_KEY[c] \cup MC_CLIENT_WRITE_KEY[c]]

MC_CLIENT_PRIMARY == [c \in MC_CLIENT |->
                        CASE c = c1 -> k1
                          [] c = c2 -> k1
                          [] c = c3 -> k2]

CurrentConfig == [ key            |-> MC_KEY,
                   client         |-> MC_CLIENT,
                   optimistic     |-> MC_OPTIMISTIC_CLIENT,
                   pessimistic    |-> MC_PESSIMISTIC_CLIENT,
                   readKey        |-> MC_CLIENT_READ_KEY,
                   writeKey       |-> MC_CLIENT_WRITE_KEY,
                   primary        |-> MC_CLIENT_PRIMARY ]

-----------------------------------------------------------------------------
(* Trivial behavior: the configuration never changes *)

Init == config = CurrentConfig

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Sanity invariants on the configuration *)

\* Every client is either optimistic or pessimistic, and not both.
ClientPartition ==
    /\ config.optimistic \cup config.pessimistic = config.client
    /\ config.optimistic \cap config.pessimistic = {}

\* Read and write key sets are subsets of the declared keys.
KeysWellFormed ==
    \A c \in config.client :
        /\ config.readKey[c] \subseteq config.key
        /\ config.writeKey[c] \subseteq config.key

\* Each client's primary key is one of the keys it writes.
PrimaryWellFormed ==
    \A c \in config.client :
        /\ config.primary[c] \in config.key
        /\ config.primary[c] \in config.writeKey[c]

\* The configuration stays fixed.
ConfigConstant == config = CurrentConfig

ConfigInvariant ==
    /\ ClientPartition
    /\ KeysWellFormed
    /\ PrimaryWellFormed
    /\ ConfigConstant

THEOREM Spec => []ConfigInvariant
=============================================================================