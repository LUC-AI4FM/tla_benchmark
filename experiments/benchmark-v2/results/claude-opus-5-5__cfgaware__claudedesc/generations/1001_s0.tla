---------------------------- MODULE APABarrier ----------------------------
(***************************************************************************)
(* Type-annotated wrapper for a barrier synchronization specification,     *)
(* intended for use with the Apalache model checker. The barrier           *)
(* definitions are inlined here so that the module is self-contained.      *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Int;
    N

VARIABLES
    \* @type: Int -> Str;
    pc

vars == << pc >>

ProcSet == 1..N

(***************************************************************************)
(* Program counter values:                                                 *)
(*   "b0" : working before the barrier                                     *)
(*   "b1" : arrived at the barrier, waiting                                *)
(*   "b2" : passed the barrier                                             *)
(***************************************************************************)
Labels == {"b0", "b1", "b2"}

Init == pc = [p \in ProcSet |-> "b0"]

\* A process reaches the barrier and starts waiting.
Arrive(p) ==
    /\ pc[p] = "b0"
    /\ pc' = [pc EXCEPT ![p] = "b1"]

\* A waiting process may pass once every process has arrived.
Pass(p) ==
    /\ pc[p] = "b1"
    /\ \A q \in ProcSet : pc[q] \in {"b1", "b2"}
    /\ pc' = [pc EXCEPT ![p] = "b2"]

\* Once all processes have passed, the barrier is reset for the next round.
Reset ==
    /\ \A q \in ProcSet : pc[q] = "b2"
    /\ pc' = [p \in ProcSet |-> "b0"]

Next ==
    \/ \E p \in ProcSet : Arrive(p) \/ Pass(p)
    \/ Reset

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
    /\ DOMAIN pc = ProcSet
    /\ \A p \in ProcSet : pc[p] \in Labels

\* Safety: no process passes the barrier while another has not yet arrived.
BarrierSafety ==
    \A p \in ProcSet :
        pc[p] = "b2" => \A q \in ProcSet : pc[q] \in {"b1", "b2"}

=============================================================================