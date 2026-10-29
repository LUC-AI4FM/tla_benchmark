---------------------------- MODULE MC_DistributedTransaction ----------------------------
(***************************************************************************)
(* Configuration layer for the DistributedTransaction specification.      *)
(* It declares two keys and three clients and defines which clients are    *)
(* optimistic or pessimistic, which keys each client reads and writes, and *)
(* the primary key of each client.                                         *)
(*                                                                         *)
(* The module has no system actions of its own. A trivial stuttering       *)
(* behavior is included only so that the module has Init, Next and Spec    *)
(* and the configuration invariants can be checked on their own.           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS k1, k2
CONSTANTS c1, c2, c3

ASSUME k1 # k2
ASSUME c1 # c2 /\ c2 # c3 /\ c1 # c3

-----------------------------------------------------------------------------
(* Keys and clients *)

const_KEY == {k1, k2}

const_CLIENT == {c1, c2, c3}

(* Optimistic and pessimistic clients *)

const_OPTIMISTIC_CLIENT == {c1, c2}

const_PESSIMISTIC_CLIENT == {c3}

(* Keys each client may read *)

const_CLIENT_READ_KEY ==
    [c \in const_CLIENT |->
        CASE c = c1 -> {k1}
          [] c = c2 -> {k1, k2}
          [] c = c3 -> {k2}]

(* Keys each client may write *)

const_CLIENT_WRITE_KEY ==
    [c \in const_CLIENT |->
        CASE c = c1 -> {k1, k2}
          [] c = c2 -> {k2}
          [] c = c3 -> {k1, k2}]

(* Primary key of each client, chosen from its write keys *)

const_CLIENT_PRIMARY ==
    [c \in const_CLIENT |->
        CASE c = c1 -> k1
          [] c = c2 -> k2
          [] c = c3 -> k1]

-----------------------------------------------------------------------------
(* Well-formedness conditions on the configuration *)

ClientPartition ==
    /\ const_OPTIMISTIC_CLIENT \cup const_PESSIMISTIC_CLIENT = const_CLIENT
    /\ const_OPTIMISTIC_CLIENT \cap const_PESSIMISTIC_CLIENT = {}

ReadKeysValid ==
    \A c \in const_CLIENT : const_CLIENT_READ_KEY[c] \subseteq const_KEY

WriteKeysValid ==
    \A c \in const_CLIENT :
        /\ const_CLIENT_WRITE_KEY[c] \subseteq const_KEY
        /\ const_CLIENT_WRITE_KEY[c] # {}

PrimaryValid ==
    \A c \in const_CLIENT : const_CLIENT_PRIMARY[c] \in const_CLIENT_WRITE_KEY[c]

ConfigurationOK ==
    /\ ClientPartition
    /\ ReadKeysValid
    /\ WriteKeysValid
    /\ PrimaryValid

ASSUME ConfigurationOK

-----------------------------------------------------------------------------
(* Trivial behavior: this module defines no system actions *)

VARIABLE configured

vars == <<configured>>

Init == configured = TRUE

Next == UNCHANGED configured

Spec == Init /\ [][Next]_vars

TypeOK == configured \in BOOLEAN

ConfigInvariant == configured => ConfigurationOK

=============================================================================