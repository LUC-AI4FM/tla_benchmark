------------------------------- MODULE APBarrier -------------------------------
(***************************************************************************)
(* Wrapper that attaches Apalache type annotations to a barrier            *)
(* specification. It declares the constant N and the variable pc, and      *)
(* redefines vars as << pc >> with an explicit type so that the 1-tuple's  *)
(* type is unambiguous. The barrier behaviour is written out here so that  *)
(* the module is self-contained and parses with SANY.                      *)
(***************************************************************************)
EXTENDS Integers

CONSTANT
    \* @type: Int;
    N

ASSUME NAssump == N \in Nat \ {0}

VARIABLE
    \* @type: Int -> Str;
    pc

\* Apalache cannot infer the type of a 1-tuple, so state it explicitly.
\* @type: <<Int -> Str>>;
vars == << pc >>

\* @type: Set(Int);
ProcSet == 1..N

(***************************************************************************)
(* Process states:                                                         *)
(*   "a" : working, has not yet arrived at the barrier                     *)
(*   "b" : arrived at the barrier, waiting                                 *)
(*   "c" : released from the barrier                                       *)
(***************************************************************************)
TypeOK == pc \in [ProcSet -> {"a", "b", "c"}]

Init == pc = [p \in ProcSet |-> "a"]

\* A process arrives at the barrier, but only after every process has left
\* the released state of the previous round.
\* @type: Int => Bool;
Arrive(p) ==
    /\ pc[p] = "a"
    /\ \A q \in ProcSet : pc[q] # "c"
    /\ pc' = [pc EXCEPT ![p] = "b"]

\* A process passes the barrier only when every process has arrived.
\* @type: Int => Bool;
Pass(p) ==
    /\ pc[p] = "b"
    /\ \A q \in ProcSet : pc[q] \in {"b", "c"}
    /\ pc' = [pc EXCEPT ![p] = "c"]

\* A process starts the next round only when every process has passed.
\* @type: Int => Bool;
Reset(p) ==
    /\ pc[p] = "c"
    /\ \A q \in ProcSet : pc[q] \in {"c", "a"}
    /\ pc' = [pc EXCEPT ![p] = "a"]

\* @type: Int => Bool;
proc(p) == Arrive(p) \/ Pass(p) \/ Reset(p)

Next == \E p \in ProcSet : proc(p)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A p \in ProcSet : WF_vars(proc(p))

(***************************************************************************)
(* Safety: the barrier is never "split": no process can pass the barrier   *)
(* while another has not yet arrived, i.e. the three phases never coexist. *)
(***************************************************************************)
BarrierSafety ==
    ~ \E p, q, r \in ProcSet :
        /\ pc[p] = "a"
        /\ pc[q] = "b"
        /\ pc[r] = "c"

\* Nobody passes while someone in the same round is still working.
NoEarlyPass ==
    (\E p \in ProcSet : pc[p] = "b") =>
        ~ \E p, q \in ProcSet : pc[p] = "c" /\ pc[q] = "a"

Inv == TypeOK /\ BarrierSafety /\ NoEarlyPass

(***************************************************************************)
(* Liveness: every process passes the barrier infinitely often.            *)
(***************************************************************************)
Progress == \A p \in ProcSet : []<>(pc[p] = "c")

THEOREM Spec => []Inv
=============================================================================