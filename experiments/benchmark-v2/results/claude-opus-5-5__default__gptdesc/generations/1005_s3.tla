-------------------------- MODULE bcastFolklore_typed --------------------------
(*****************************************************************************)
(* A thin wrapper that supplies Apalache type annotations for the           *)
(* specification bcastFolklore. Constants and variables are declared here    *)
(* with Apalache type comments, and the original module is instantiated.    *)
(* This keeps bcastFolklore free of tool-specific annotations.              *)
(*                                                                           *)
(* This module defines no behavior of its own. Every definition of          *)
(* bcastFolklore is imported unchanged by the unnamed INSTANCE below. That  *)
(* includes Init, Next, Spec, the fairness conditions, and the safety and   *)
(* liveness properties.                                                     *)
(*****************************************************************************)

EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Int;
    N,          \* number of processes
    \* @type: Int;
    T,          \* upper bound on the number of faulty processes
    \* @type: Int;
    F           \* actual number of crashed processes

VARIABLES
    \* @type: Set(Int);
    Corr,       \* set of correct (non-crashed) processes
    \* @type: Int;
    nCrashed,   \* number of processes that have crashed so far
    \* @type: Int -> Str;
    pc,         \* control state of each process: "V0", "V1", "AC", "CR"
    \* @type: Int -> Set(<<Int, Str>>);
    rcvd,       \* messages received by each process
    \* @type: Set(<<Int, Str>>);
    sent        \* messages sent by all processes

\* Import Init, Next, Spec, fairness, invariants and temporal properties
\* from the original, annotation-free specification.
INSTANCE bcastFolklore

================================================================================