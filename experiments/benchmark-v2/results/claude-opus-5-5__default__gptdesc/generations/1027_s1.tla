--------------------------- MODULE MC_apalache ---------------------------
(***************************************************************************)
(* Apalache wrapper for the Chang-Roberts leader election specification.  *)
(* Holds the type annotations and concrete constant values; Init, Next,   *)
(* Spec, invariants and properties come from the instantiated module      *)
(* ChangRoberts, which is not redefined here.                             *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    \* @type: Int;
    N,
    \* @type: Seq(Int);
    Id

VARIABLES
    \* @type: Int -> Set(Int);
    msgs,
    \* @type: Int -> Str;
    pc,
    \* @type: Int -> Bool;
    initiator,
    \* @type: Int -> Str;
    state

\* Concrete value for the ring size N
NVal == 3

\* Concrete value for the identifier sequence Id
IdVal == <<3, 1, 2>>

\* Import Init, Next, Spec, TypeOK, Correctness, Liveness, etc.
INSTANCE ChangRoberts

=============================================================================