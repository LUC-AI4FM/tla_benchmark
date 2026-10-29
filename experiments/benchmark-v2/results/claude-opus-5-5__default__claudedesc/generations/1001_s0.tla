------------------------------- MODULE APABarrier -------------------------------
(***************************************************************************)
(* Type-annotated wrapper for the Barrier specification, for use with the *)
(* Apalache model checker. In the original design the wrapper consists of *)
(* the annotated declarations followed by                                  *)
(*                                                                         *)
(*     INSTANCE Barrier                                                    *)
(*                                                                         *)
(* Here the Barrier definitions are written out inline so the module is    *)
(* self-contained and passes SANY on its own.                              *)
(*                                                                         *)
(* Model-checking configuration:                                           *)
(*     CONSTANT  N = 6                                                     *)
(*     SPECIFICATION Spec                                                  *)
(*     INVARIANT TypeOK                                                    *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
    \* @type: Int;
    N

VARIABLES
    \* @type: Int -> Str;
    pc

vars == << pc >>

ASSUME NAssumption == N \in Nat \ {0}

ProcSet == 1..N

(***************************************************************************)
(* Program counter values:                                                 *)
(*   "a" : working before the barrier                                      *)
(*   "b" : arrived at the barrier, waiting                                 *)
(*   "c" : passed the barrier                                              *)
(***************************************************************************)
PCValues == {"a", "b", "c"}

TypeOK == pc \in [ProcSet -> PCValues]

Init == pc = [p \in ProcSet |-> "a"]

(* A process arrives at the barrier. No process may still be leaving the  *)
(* previous round.                                                        *)
Arrive(p) ==
    /\ pc[p] = "a"
    /\ \A q \in ProcSet : pc[q] # "c"
    /\ pc' = [pc EXCEPT ![p] = "b"]

(* A process passes the barrier once every process has arrived.           *)
Pass(p) ==
    /\ pc[p] = "b"
    /\ \A q \in ProcSet : pc[q] \in {"b", "c"}
    /\ pc' = [pc EXCEPT ![p] = "c"]

(* A process that has passed returns to work once no process is waiting. *)
Reset(p) ==
    /\ pc[p] = "c"
    /\ \A q \in ProcSet : pc[q] \in {"a", "c"}
    /\ pc' = [pc EXCEPT ![p] = "a"]

proc(p) == Arrive(p) \/ Pass(p) \/ Reset(p)

Next == \E p \in ProcSet : proc(p)

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ \A p \in ProcSet : WF_vars(proc(p))

(* Barrier safety: no process passes the barrier while another has not  *)
(* yet arrived in the current round.                                     *)
BarrierSafety ==
    \A p, q \in ProcSet : (pc[p] = "c") => (pc[q] # "a" \/ \A r \in ProcSet : pc[r] # "b")

THEOREM Spec => []TypeOK
=================================================================================