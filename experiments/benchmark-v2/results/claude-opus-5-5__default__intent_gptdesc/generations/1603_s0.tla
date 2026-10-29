---------------------------- MODULE SingleComputation ----------------------------
EXTENDS Integers

(***************************************************************************)
(* Reusable component. It is declared as a separate module and used only  *)
(* through an INSTANCE. It returns a deterministic numeric result that     *)
(* depends only on the constants supplied when it is instantiated.         *)
(***************************************************************************)
---------------------------- MODULE Component ----------------------------
EXTENDS Integers
CONSTANTS CompArg1, CompArg2

\* The component's deterministic output. Only its value matters here; how
\* it is implemented is left abstract.
Result == CompArg1 + CompArg2
==========================================================================