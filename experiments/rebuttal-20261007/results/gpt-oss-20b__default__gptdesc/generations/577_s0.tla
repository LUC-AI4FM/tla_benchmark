MODULE AlternativeInitialState
EXTENDS BaseSpec

VARIABLES vars

(* ------------------------------------------------------------------ *)
(*  Initial state that pre-populates two committed transactions        *)
(* ------------------------------------------------------------------ *)

Init ==
  /\ BaseSpec.Init
  /\ ledgerBranches = [node1 |-> [], node2 |-> []]
  /\ history =
       << [txId |-> 1, response |-> "ok", committedStatus |-> TRUE],
          [txId |-> 2, response |-> "ok", committedStatus |-> TRUE] >>

(* ------------------------------------------------------------------ *)
(*  Next action from the base specification                          *)
(* ------------------------------------------------------------------ *)

Next == MCNextMultiNodeReadsAction

(* ------------------------------------------------------------------ *)
(*  Temporal specification starting from the alternative initial state*)
(* ------------------------------------------------------------------ *)

Spec == Init /\ [][Next]_vars
===============================================================================