---------------------------- MODULE bcastFolklore_typedefs ----------------------------
(*
 * A thin wrapper that adds Apalache type annotations to the specification
 * bcastFolklore. The original specification stays free of tool-specific
 * annotations. All declarations are passed to bcastFolklore through INSTANCE,
 * and this module defines no behavior of its own. Init, Next and Spec only
 * delegate to the instantiated module.
 *)

EXTENDS Naturals, FiniteSets

CONSTANTS
    \* @type: Int;
    N,      \* the number of processes
    \* @type: Int;
    T,      \* an upper bound on the number of faulty processes
    \* @type: Int;
    F       \* the actual number of faulty processes

VARIABLES
    \* @type: Int -> Str;
    pc,     \* the control state of each process
    \* @type: Int -> Set(<<Int, Str>>);
    rcvd,   \* the messages received by each process
    \* @type: Set(<<Int, Str>>);
    sent    \* the messages sent by all correct processes

vars == << pc, rcvd, sent >>

\* Instantiate the original, annotation-free specification.
\* The constants and variables are substituted implicitly by name.
BF == INSTANCE bcastFolklore

\* Delegations only. This module adds no behavior of its own.
Init == BF!Init

Next == BF!Next

Spec == BF!Spec

=============================================================================