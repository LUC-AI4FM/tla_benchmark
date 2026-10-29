---------------------------- MODULE MC_DistributedTransaction ----------------------------
(***************************************************************************)
(* Small configuration for the DistributedTransaction specification.      *)
(* Declares two keys and three clients, and defines which clients are     *)
(* optimistic or pessimistic, which keys each client may read or write,   *)
(* and the primary key of each client.                                    *)
(*                                                                         *)
(* This module is a parameterization layer only. So that it parses on its *)
(* own, it does not EXTEND DistributedTransaction. Instead it includes a  *)
(* trivial stuttering behavior over a single configuration variable, and  *)
(* invariants that check the configuration is well formed.                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS k1, k2
CONSTANTS c1, c2, c3

VARIABLES config

vars == << config >>

-----------------------------------------------------------------------------
(* Configuration constants *)

const_KEY == {k1, k2}

const_CLIENT == {c1, c2, c3}

const_OPTIMISTIC_CLIENT == {c1}

const_PESSIMISTIC_CLIENT == {c2, c3}

const_CLIENT_READ_KEY == (c1 :> {k1, k2}) @@ (c2 :> {k1}) @@ (c3 :> {k2})

const_CLIENT_WRITE_KEY == (c1 :> {k1, k2}) @@ (c2 :> {k1, k2}) @@ (c3 :> {k2})

const_CLIENT_PRIMARY == (c1 :> k1) @@ (c2 :> k2) @@ (c3 :> k2)

-----------------------------------------------------------------------------
(* Well-formedness of the configuration *)

ConfigWellFormed ==
  /\ const_OPTIMISTIC_CLIENT \cup const_PESSIMISTIC_CLIENT = const_CLIENT
  /\ const_OPTIMISTIC_CLIENT \cap const_PESSIMISTIC_CLIENT = {}
  /\ DOMAIN const_CLIENT_READ_KEY = const_CLIENT
  /\ DOMAIN const_CLIENT_WRITE_KEY = const_CLIENT
  /\ DOMAIN const_CLIENT_PRIMARY = const_CLIENT
  /\ \A c \in const_CLIENT :
        /\ const_CLIENT_READ_KEY[c] \subseteq const_KEY
        /\ const_CLIENT_WRITE_KEY[c] \subseteq const_KEY
        /\ const_CLIENT_PRIMARY[c] \in const_CLIENT_WRITE_KEY[c]

-----------------------------------------------------------------------------
(* Trivial behavior: the configuration is fixed and never changes *)

ConfigRecord ==
  [ key        |-> const_KEY,
    optimistic |-> const_OPTIMISTIC_CLIENT,
    pessimistic|-> const_PESSIMISTIC_CLIENT,
    readKey    |-> const_CLIENT_READ_KEY,
    writeKey   |-> const_CLIENT_WRITE_KEY,
    primary    |-> const_CLIENT_PRIMARY ]

Init == config = ConfigRecord

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK == config = ConfigRecord

ConfigInvariant == ConfigWellFormed

=============================================================================