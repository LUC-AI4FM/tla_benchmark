------------------------- MODULE APAnbacg_guer01 -------------------------
(***************************************************************************)
(* Apalache type-annotation wrapper for nbacg_guer01.                      *)
(*                                                                         *)
(* This module only declares the constant and state variables with         *)
(* Apalache type annotations, and then instantiates the original           *)
(* specification nbacg_guer01. The original module is left unchanged.      *)
(* Init, Next, Spec, the invariants and the temporal properties are all    *)
(* imported from nbacg_guer01 through the INSTANCE statement below.        *)
(***************************************************************************)

EXTENDS Integers

CONSTANT
    \* @type: Int;
    N

VARIABLES
    \* number of NO messages sent by non-failed processes
    \* @type: Int;
    nSntNo,
    \* number of YES messages sent by non-failed processes
    \* @type: Int;
    nSntYes,
    \* number of NO messages sent by processes that later failed
    \* @type: Int;
    nSntNoF,
    \* number of YES messages sent by processes that later failed
    \* @type: Int;
    nSntYesF,
    \* number of YES messages received by each process
    \* @type: Int -> Int;
    nRcvdYes,
    \* number of NO messages received by each process
    \* @type: Int -> Int;
    nRcvdNo,
    \* failure-detector flag for each process
    \* @type: Int -> Bool;
    someFail,
    \* program counter of each process
    \* @type: Int -> Str;
    pc

INSTANCE nbacg_guer01

==========================================================================