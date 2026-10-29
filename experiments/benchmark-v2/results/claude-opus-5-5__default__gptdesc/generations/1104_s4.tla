------------------------- MODULE APAnbacg_guer01 ---------------------------
(*
 * This is an Apalache type-annotation wrapper around nbacg_guer01.tla.
 * The original module is not modified. Instead, this module declares
 * the constants and the state variables with Apalache type annotations
 * and then instantiates nbacg_guer01.
 *
 * All operators of the wrapped protocol, including Init, Next, Spec,
 * the invariants, the fairness conditions and the temporal properties,
 * come from the INSTANCE below. They are not redefined here, because
 * redefining them would clash with the instantiated definitions.
 *)

EXTENDS Integers

CONSTANT
  \* @type: Int;
  N

VARIABLES
  \* the number of NO messages sent by correct processes
  \* @type: Int;
  nSntNo,
  \* the number of YES messages sent by correct processes
  \* @type: Int;
  nSntYes,
  \* the number of NO messages sent by processes that later crash
  \* @type: Int;
  nSntNoF,
  \* the number of YES messages sent by processes that later crash
  \* @type: Int;
  nSntYesF,
  \* the number of YES messages received by each process
  \* @type: Int -> Int;
  nRcvdYes,
  \* the number of NO messages received by each process
  \* @type: Int -> Int;
  nRcvdNo,
  \* whether the failure detector of a process has reported a crash
  \* @type: Int -> Bool;
  someFail,
  \* the program counter of each process
  \* @type: Int -> Str;
  pc

INSTANCE nbacg_guer01

=============================================================================