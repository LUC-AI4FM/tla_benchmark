--------------------------- MODULE Peterson ---------------------------
(***************************************************************************)
(* Peterson's mutual exclusion algorithm for two processes, 0 and 1.       *)
(*                                                                         *)
(* --algorithm Peterson {                                                  *)
(*    variables c = [i \in {0,1} |-> FALSE], turn = 0;                     *)
(*    fair process (proc \in {0,1}) {                                      *)
(*      a0: while (TRUE) {                                                 *)
(*            skip ;                     \* noncritical section            *)
(*      a1:   c[self] := TRUE ;                                            *)
(*      a2:   turn := Not(self) ;                                          *)
(*      a3:   await (~ c[Not(self)]) \/ (turn = self) ;                    *)
(*      cs:   skip ;                     \* critical section               *)
(*      a4:   c[self] := FALSE ;                                           *)
(*          }                                                              *)
(*    }                                                                    *)
(* }                                                                       *)
(***************************************************************************)
EXTENDS Integers

(***************************************************************************)
(* Abstract lock specification, used as the target of a refinement.       *)
(***************************************************************************)
---------------------------- MODULE Lock ----------------------------------
CONSTANT Procs
VARIABLE lpc

LInit == lpc = [p \in Procs |-> "out"]

Acquire(p) == /\ lpc[p] = "out"
              /\ \A q \in Procs : lpc[q] # "in"
              /\ lpc' = [lpc EXCEPT ![p] = "in"]

Release(p) == /\ lpc[p] = "in"
              /\ lpc' = [lpc EXCEPT ![p] = "out"]

LNext == \E p \in Procs : Acquire(p) \/ Release(p)

LSpec == LInit /\ [][LNext]_lpc

LMutex == \A p, q \in Procs : (lpc[p] = "in" /\ lpc[q] = "in") => p = q
============================================================================