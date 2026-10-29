------------------------------ MODULE APBarrier ------------------------------
(***************************************************************************)
(* A lightweight wrapper whose purpose is to attach Apalache type          *)
(* annotations to a barrier specification. It declares the constant N and *)
(* the variable pc. It redefines vars as << pc >> so that the type of the *)
(* 1-tuple is unambiguous.                                                 *)
(*                                                                         *)
(* The behavior of the Barrier module is restated here so that the module *)
(* is self-contained and the names TypeOK and Spec are defined for the    *)
(* model-checking configuration.                                           *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Int;
    N

VARIABLE
    \* @type: Int -> Str;
    pc

\* @type: <<Int -> Str>>;
vars == << pc >>

ProcSet == 1..N

TypeOK == pc \in [ProcSet -> {"b0", "b1", "b2"}]

Init == pc = [p \in ProcSet |-> "b0"]

(* A process arrives at the barrier. *)
Arrive(p) ==
    /\ pc[p] = "b0"
    /\ pc' = [pc EXCEPT ![p] = "b1"]

(* A process passes the barrier once every process has arrived. *)
Pass(p) ==
    /\ pc[p] = "b1"
    /\ \A q \in ProcSet : pc[q] \in {"b1", "b2"}
    /\ pc' = [pc EXCEPT ![p] = "b2"]

(* A process resets for the next round once every process has passed. *)
Reset(p) ==
    /\ pc[p] = "b2"
    /\ \A q \in ProcSet : pc[q] \in {"b2", "b0"}
    /\ pc' = [pc EXCEPT ![p] = "b0"]

Next == \E p \in ProcSet : Arrive(p) \/ Pass(p) \/ Reset(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Safety: no process passes the barrier while another has not arrived. *)
BarrierSafety ==
    \A p \in ProcSet : pc[p] = "b2" => \A q \in ProcSet : pc[q] # "b0" \/ \A r \in ProcSet : pc[r] \in {"b0", "b2"}

=============================================================================