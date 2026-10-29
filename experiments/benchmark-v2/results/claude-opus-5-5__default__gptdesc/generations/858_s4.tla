------------------------- MODULE APAReadersWriters -------------------------
(***************************************************************************)
(* Apalache type annotations for the ReadersWriters specification.        *)
(*                                                                         *)
(* This module declares the constants and state variables of the          *)
(* ReadersWriters specification with concrete Apalache types. It then     *)
(* instantiates the original ReadersWriters module. The instantiated      *)
(* module supplies Init, Next, Spec and the safety and liveness           *)
(* properties. This module defines no transitions, temporal properties    *)
(* or proofs of its own.                                                   *)
(*                                                                         *)
(* The duplicate-definition trick: Apalache needs monomorphic types for    *)
(* the helper operators is_read, is_write and ToSet. In ReadersWriters     *)
(* these operators are polymorphic, or they cannot be annotated in place.  *)
(* So this module redefines them here with type annotations and with       *)
(* bodies that are exactly the same as the originals. SANY accepts the    *)
(* repeated definitions because the bodies match. Apalache then uses the   *)
(* annotated versions. The bodies must stay identical to the original      *)
(* definitions. If they differ, the parser rejects the redefinition, or    *)
(* the checked semantics would differ from the original spec.              *)
(***************************************************************************)
EXTENDS Naturals, Sequences

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

\* Duplicate definitions with the same bodies as in ReadersWriters,
\* given monomorphic types so that Apalache can check them.

\* @type: (<<Str, Int>>) => Bool;
is_read(p) == p[1] = "read"

\* @type: (<<Str, Int>>) => Bool;
is_write(p) == p[1] = "write"

\* @type: (Seq(<<Str, Int>>)) => Set(<<Str, Int>>);
ToSet(s) == { s[i] : i \in DOMAIN s }

\* Instantiate the original specification. Init, Next, Spec, the safety
\* invariants, the liveness properties and the fairness conditions all
\* come from the ReadersWriters module.
INSTANCE ReadersWriters

=============================================================================