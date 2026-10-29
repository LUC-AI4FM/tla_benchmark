------------------------- MODULE APAReadersWriters -------------------------
(***************************************************************************)
(* Apalache-specific wrapper for the ReadersWriters specification.         *)
(*                                                                         *)
(* Apalache needs concrete, monomorphic type annotations for every state   *)
(* variable, constant and operator. The original ReadersWriters module is  *)
(* left untyped, so this module declares the same constants and variables  *)
(* with type annotations. It also redefines the few polymorphic helper     *)
(* operators with concrete types, and then instantiates ReadersWriters.    *)
(*                                                                         *)
(* NOTE on the duplicate-definition trick: the helper operators ToSet,     *)
(* read and write below are also defined in ReadersWriters. SANY accepts   *)
(* the duplicate definitions because the operator bodies are textually     *)
(* identical. Apalache then picks up the monomorphic type annotations      *)
(* given here. Do NOT change the operator bodies: they must stay exactly   *)
(* identical to the definitions in ReadersWriters.                         *)
(*                                                                         *)
(* This module defines no transitions, temporal properties or proofs of    *)
(* its own. Init, Next, Spec, the invariants and the liveness properties   *)
(* all come from the instantiated ReadersWriters module.                   *)
(***************************************************************************)
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT
    \* @type: Int;
    NumActors

VARIABLES
    \* @type: Set(Int);
    readers,
    \* @type: Set(Int);
    writers,
    \* @type: Seq(<<Str, Int>>);
    waiting

----------------------------------------------------------------------------
(***************************************************************************)
(* Helper operators with concrete (monomorphic) types for Apalache.        *)
(* The bodies are identical to those in ReadersWriters (duplicate          *)
(* definition trick).                                                      *)
(***************************************************************************)

\* Convert a sequence of queue entries into the set of its elements.
\* @type: Seq(<<Str, Int>>) => Set(<<Str, Int>>);
ToSet(s) == { s[i] : i \in DOMAIN s }

\* A queue entry is a read request.
\* @type: <<Str, Int>> => Bool;
read(s) == s[1] = "read"

\* A queue entry is a write request.
\* @type: <<Str, Int>> => Bool;
write(s) == s[1] = "write"

----------------------------------------------------------------------------
(***************************************************************************)
(* Instantiate the original specification. Init, Next, Spec, the safety    *)
(* invariants, the liveness properties and the fairness conditions are     *)
(* all imported from ReadersWriters.                                       *)
(***************************************************************************)
INSTANCE ReadersWriters

=============================================================================