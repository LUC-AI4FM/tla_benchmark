------------------------- MODULE APAbcastFolklore -----------------------------
(*
 * Apalache type annotations for the specification bcastFolklore.
 *
 * This module only declares the constants and variables of bcastFolklore,
 * annotated with Apalache types, and instantiates bcastFolklore. All
 * definitions of bcastFolklore, including Init, Next, Spec, fairness
 * conditions, invariants and temporal properties, are imported unchanged
 * through the INSTANCE declaration. The original specification therefore
 * stays free of tool-specific annotations.
 *)

EXTENDS Naturals, FiniteSets

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

\* Import every definition of bcastFolklore (Init, Next, Spec, fairness,
\* safety invariants and liveness properties) with the parameters above.
INSTANCE bcastFolklore

===============================================================================