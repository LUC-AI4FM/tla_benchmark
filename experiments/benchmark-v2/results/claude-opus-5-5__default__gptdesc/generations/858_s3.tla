-------------------------- MODULE APAReadersWriters --------------------------
(***************************************************************************)
(* Apalache-specific wrapper around the ReadersWriters specification.      *)
(*                                                                         *)
(* Apalache needs concrete, monomorphic types for every operator. The      *)
(* original ReadersWriters module defines a few polymorphic helpers. To    *)
(* satisfy Apalache, we redefine those helpers here with type annotations  *)
(* and then instantiate the original module.                               *)
(*                                                                         *)
(* NOTE: This is a duplicate-definition trick. The operator bodies below   *)
(* are identical to the ones in ReadersWriters. Because the definitions    *)
(* are identical, the instantiation is accepted. Apalache uses the typed   *)
(* versions given here.                                                    *)
(*                                                                         *)
(* This module defines no transitions, temporal properties, or proofs of   *)
(* its own. Init, Next, Spec, the invariants and the liveness properties   *)
(* are all inherited from ReadersWriters through the INSTANCE below.       *)
(***************************************************************************)
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT
    \* @type: Int;
    NumActors

VARIABLES
    \* @type: Set(Int);
    readers,  \* set of processes currently reading
    \* @type: Set(Int);
    writers,  \* set of processes currently writing
    \* @type: Seq(<<Str, Int>>);
    waiting   \* queue of processes waiting to access the resource

\* Duplicate definitions with monomorphic types for Apalache.
\* The bodies are identical to those in ReadersWriters.

\* @type: <<Str, Int>> => Bool;
is_read(p) == p[1] = "read"

\* @type: <<Str, Int>> => Bool;
is_write(p) == p[1] = "write"

\* @type: Seq(<<Str, Int>>) => Set(<<Str, Int>>);
ToSet(s) == { s[i] : i \in DOMAIN s }

INSTANCE ReadersWriters

==============================================================================