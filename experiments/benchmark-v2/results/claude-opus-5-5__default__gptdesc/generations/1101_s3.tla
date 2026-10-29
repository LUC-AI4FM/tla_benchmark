------------------------------ MODULE Peterson ------------------------------
(***************************************************************************)
(* Peterson's mutual exclusion algorithm for two processes, 0 and 1.      *)
(*                                                                         *)
(* --algorithm Peterson {                                                  *)
(*    variables c = [i \in {0,1} |-> FALSE], turn = 0;                     *)
(*    fair process (proc \in {0,1}) {                                      *)
(*      a0: while (TRUE) {                                                 *)
(*      a1:   c[self] := TRUE;                                             *)
(*      a2:   turn := Not(self);                                           *)
(*      a3:   await (~ c[Not(self)]) \/ (turn = self);                     *)
(*      cs:   skip;   \* critical section                                  *)
(*      a4:   c[self] := FALSE;                                            *)
(*          }                                                              *)
(*    }                                                                    *)
(* }                                                                       *)
(***************************************************************************)
EXTENDS Naturals

(***************************************************************************)
(* Abstract lock specification, used as the target of a refinement.       *)
(***************************************************************************)
---------------------------------- MODULE Lock ----------------------------------
CONSTANT Procs
VARIABLES pc, lock

lvars == <<pc, lock>>

LInit == /\ pc = [p \in Procs |-> "a0"]
         /\ lock = 1

la0(self) == /\ pc[self] = "a0"
             /\ pc' = [pc EXCEPT ![self] = "a1"]
             /\ UNCHANGED lock

la1(self) == /\ pc[self] = "a1"
             /\ lock = 1
             /\ lock' = 0
             /\ pc' = [pc EXCEPT ![self] = "cs"]

lcs(self) == /\ pc[self] = "cs"
             /\ pc' = [pc EXCEPT ![self] = "a2"]
             /\ UNCHANGED lock

la2(self) == /\ pc[self] = "a2"
             /\ lock' = 1
             /\ pc' = [pc EXCEPT ![self] = "a0"]

LNext == \E self \in Procs : la0(self) \/ la1(self) \/ lcs(self) \/ la2(self)

LSpec == LInit /\ [][LNext]_lvars

LMutex == \A p, q \in Procs : (pc[p] \in {"cs","a2"} /\ pc[q] \in {"cs","a2"}) => p = q
=================================================================================