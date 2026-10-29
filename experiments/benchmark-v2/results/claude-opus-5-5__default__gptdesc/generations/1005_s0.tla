--------------------------- MODULE APAbcastFolklore ---------------------------
(*****************************************************************************)
(* Apalache type annotations for the specification bcastFolklore.           *)
(*                                                                           *)
(* This module only declares the constants and variables of bcastFolklore   *)
(* together with their Apalache types, and then instantiates bcastFolklore. *)
(* All definitions of the instantiated module (Init, Next, Spec, the        *)
(* invariants and the temporal properties) become available here through   *)
(* the INSTANCE declaration. This keeps the original specification free of  *)
(* tool-specific annotations.                                               *)
(*****************************************************************************)

EXTENDS Naturals

CONSTANTS
    \* @type: Int;
    N,
    \* @type: Int;
    T,
    \* @type: Int;
    F

VARIABLES
    \* @type: Set(Int);
    Corr,
    \* @type: Int;
    nCrashed,
    \* @type: Int -> Str;
    pc,
    \* @type: Int -> Set(<<Int, Str>>);
    rcvd,
    \* @type: Set(<<Int, Str>>);
    sent

INSTANCE bcastFolklore

===============================================================================