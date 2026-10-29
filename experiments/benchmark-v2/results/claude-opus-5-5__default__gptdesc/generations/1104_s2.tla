------------------------- MODULE APAnbacg_guer01 -------------------------
(*
 * Apalache type-annotation wrapper for the specification nbacg_guer01.
 *
 * This module declares the constant N and the state variables of the
 * wrapped protocol, annotated with Apalache types. The original module
 * nbacg_guer01 is brought in unchanged by INSTANCE. Init, Next, Spec, the
 * invariants, the temporal properties and the fairness conditions are all
 * defined in nbacg_guer01. INSTANCE makes them available here under their
 * original names.
 *)

EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Int;
    N

VARIABLES
    \* number of NO messages sent by correct processes
    \* @type: Int;
    nSntNo,
    \* number of YES messages sent by correct processes
    \* @type: Int;
    nSntYes,
    \* number of NO messages sent by processes that later crash
    \* @type: Int;
    nSntNoF,
    \* number of YES messages sent by processes that later crash
    \* @type: Int;
    nSntYesF,
    \* number of YES messages received by each process
    \* @type: Int -> Int;
    nRcvdYes,
    \* number of NO messages received by each process
    \* @type: Int -> Int;
    nRcvdNo,
    \* whether each process has detected a failure
    \* @type: Int -> Bool;
    someFail,
    \* program counter of each process
    \* @type: Int -> Str;
    pc

INSTANCE nbacg_guer01

=============================================================================