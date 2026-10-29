---------------------------- MODULE MCTwoClientsTwoKeys ----------------------------
(***************************************************************************)
(* A minimal setup for TLC model checking: two clients (c1, c2) and a      *)
(* table with two primary keys (1 and 2).  Each client is associated with  *)
(* a unique primary key via the ClientPrimaryKey mapping.                  *)
(*                                                                         *)
(* The original module defines no actions or temporal properties.  The     *)
(* Init / Next / Spec below are trivial placeholders: the single variable  *)
(* never changes, so every step is a stutter step.  They exist only so     *)
(* that the module is a complete, checkable specification.                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS c1, c2

ASSUME c1 # c2

\* The set of clients in the model
Clients == {c1, c2}

\* The set of primary keys in the table
PrimaryKeys == {1, 2}

\* Each client is mapped to its own unique primary key
ClientPrimaryKey == (c1 :> 1) @@ (c2 :> 2)

\* Symmetry set that TLC can use when checking the model
Symmetry == Permutations(Clients)

\* Placeholder state.  It records the table's primary keys and never changes.
VARIABLE table

vars == << table >>

TypeOK == table \in SUBSET PrimaryKeys

Init == table = PrimaryKeys

\* No actions are defined, so the only step is stuttering.
Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* Safety invariants: well-formedness of the configuration                 *)

\* ClientPrimaryKey is a function from Clients to PrimaryKeys
MappingTypeOK ==
    /\ DOMAIN ClientPrimaryKey = Clients
    /\ \A c \in Clients : ClientPrimaryKey[c] \in PrimaryKeys

\* Each client is associated with a unique primary key (injective mapping)
UniqueKeys ==
    \A a, b \in Clients : a # b => ClientPrimaryKey[a] # ClientPrimaryKey[b]

\* Every primary key in the table belongs to some client (bijection)
AllKeysAssigned ==
    \A k \in PrimaryKeys : \E c \in Clients : ClientPrimaryKey[c] = k

Inv == TypeOK /\ MappingTypeOK /\ UniqueKeys /\ AllKeysAssigned

=============================================================================