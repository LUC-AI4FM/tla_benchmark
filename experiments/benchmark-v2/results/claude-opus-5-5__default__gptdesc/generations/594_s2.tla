---------------------------- MODULE MC_DistributedTransaction ----------------------------
(***************************************************************************)
(* Small configuration for the DistributedTransaction system.              *)
(* It declares two keys and three clients and defines which clients are    *)
(* optimistic or pessimistic, which keys each client reads and writes, and *)
(* the primary key of each client. The module defines no system actions.   *)
(* Init/Next/Spec are a trivial stuttering behavior over a single dummy    *)
(* variable, so the configuration can be loaded and its well-formedness   *)
(* invariants checked on their own.                                        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

\* Keys (model values)
CONSTANTS k1, k2

\* Clients (model values)
CONSTANTS c1, c2, c3

ASSUME k1 # k2
ASSUME c1 # c2 /\ c1 # c3 /\ c2 # c3

VARIABLES configLoaded

vars == << configLoaded >>

---------------------------------------------------------------------------
(* Configuration definitions *)

const_KEY == {k1, k2}

const_OPTIMISTIC_CLIENT == {c1}

const_PESSIMISTIC_CLIENT == {c2, c3}

const_CLIENT == const_OPTIMISTIC_CLIENT \cup const_PESSIMISTIC_CLIENT

const_CLIENT_READ_KEY ==
       (c1 :> {})
    @@ (c2 :> {k1})
    @@ (c3 :> {k1, k2})

const_CLIENT_WRITE_KEY ==
       (c1 :> {k1, k2})
    @@ (c2 :> {k1})
    @@ (c3 :> {k2})

const_CLIENT_KEY ==
    [c \in const_CLIENT |-> const_CLIENT_READ_KEY[c] \cup const_CLIENT_WRITE_KEY[c]]

const_CLIENT_PRIMARY ==
       (c1 :> k1)
    @@ (c2 :> k1)
    @@ (c3 :> k2)

---------------------------------------------------------------------------
(* Well-formedness of the configuration *)

ClientsPartitioned ==
    const_OPTIMISTIC_CLIENT \cap const_PESSIMISTIC_CLIENT = {}

ClientCount == Cardinality(const_CLIENT) = 3

KeyCount == Cardinality(const_KEY) = 2

ReadKeysValid ==
    /\ DOMAIN const_CLIENT_READ_KEY = const_CLIENT
    /\ \A c \in const_CLIENT : const_CLIENT_READ_KEY[c] \subseteq const_KEY

WriteKeysValid ==
    /\ DOMAIN const_CLIENT_WRITE_KEY = const_CLIENT
    /\ \A c \in const_CLIENT : const_CLIENT_WRITE_KEY[c] \subseteq const_KEY

PrimaryValid ==
    /\ DOMAIN const_CLIENT_PRIMARY = const_CLIENT
    /\ \A c \in const_CLIENT : const_CLIENT_PRIMARY[c] \in const_CLIENT_WRITE_KEY[c]

ConfigWellFormed ==
    /\ ClientsPartitioned
    /\ ClientCount
    /\ KeyCount
    /\ ReadKeysValid
    /\ WriteKeysValid
    /\ PrimaryValid

---------------------------------------------------------------------------
(* Trivial behavior: the configuration is static *)

Init == configLoaded = TRUE

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeOK == configLoaded \in BOOLEAN

ConfigInvariant == configLoaded => ConfigWellFormed

=============================================================================