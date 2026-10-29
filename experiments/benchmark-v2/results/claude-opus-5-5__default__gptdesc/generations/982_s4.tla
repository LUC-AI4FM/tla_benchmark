-------------------------- MODULE MCYoYoNoPruning --------------------------
(***************************************************************************)
(* Model-checking wrapper for the YoYoNoPruning specification.            *)
(* The graph is fixed directly in this module and the YoYoNoPruning       *)
(* module is instantiated without substitutions. The definitions Init,    *)
(* Next and Spec, and all other operators, come from that instance.       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

VARIABLES phase, incoming, outgoing, mailbox

(***************************************************************************)
(* A small fixed graph.                                                   *)
(***************************************************************************)
Nodes == {1, 2, 3}
Edges == {{1,2}, {1,3}, {2,3}}

(***************************************************************************)
(* A larger alternative graph (commented out):                            *)
(*                                                                         *)
(* Nodes == {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13}                       *)
(* Edges == {{2,5}, {2,7}, {3,4}, {3,6}, {4,5}, {4,8}, {5,9}, {6,10},      *)
(*           {7,11}, {8,12}, {9,13}, {10,11}, {11,12}, {12,13}}            *)
(***************************************************************************)

INSTANCE YoYoNoPruning

(***************************************************************************)
(* Aliases for the instantiated specification, for use in the TLC config. *)
(***************************************************************************)
MCInit == Init
MCNext == Next
MCSpec == Spec

(***************************************************************************)
(* Liveness-style property: eventually all nodes remain permanently in    *)
(* the "down" phase.                                                      *)
(***************************************************************************)
AllDown == \A n \in Nodes : phase[n] = "down"

EventuallyAlwaysAllDown == <>[] AllDown

(***************************************************************************)
(* States of the TLC-generated counterexample.                            *)
(***************************************************************************)
CEState1 ==
    [ phase    |-> (1 :> "down" @@ 2 :> "down" @@ 3 :> "down"),
      incoming |-> (1 :> {} @@ 2 :> {1} @@ 3 :> {1, 2}),
      outgoing |-> (1 :> {2, 3} @@ 2 :> {3} @@ 3 :> {}),
      mailbox  |-> (1 :> {} @@ 2 :> {} @@ 3 :> {}) ]

CEState2 ==
    [ phase    |-> (1 :> "down" @@ 2 :> "down" @@ 3 :> "down"),
      incoming |-> (1 :> {} @@ 2 :> {1} @@ 3 :> {1, 2}),
      outgoing |-> (1 :> {2, 3} @@ 2 :> {3} @@ 3 :> {}),
      mailbox  |-> (1 :> {}
                    @@ 2 :> {[phase |-> "down", sndr |-> 1, val |-> 1]}
                    @@ 3 :> {[phase |-> "down", sndr |-> 1, val |-> 1]}) ]

CEState3 ==
    [ phase    |-> (1 :> "down" @@ 2 :> "down" @@ 3 :> "down"),
      incoming |-> (1 :> {} @@ 2 :> {1} @@ 3 :> {1, 2}),
      outgoing |-> (1 :> {2, 3} @@ 2 :> {3} @@ 3 :> {}),
      mailbox  |-> (1 :> {}
                    @@ 2 :> {[phase |-> "down", sndr |-> 1, val |-> 1]}
                    @@ 3 :> {[phase |-> "down", sndr |-> 1, val |-> 1],
                             [phase |-> "down", sndr |-> 2, val |-> 1]}) ]

CEState4 ==
    [ phase    |-> (1 :> "down" @@ 2 :> "down" @@ 3 :> "up"),
      incoming |-> (1 :> {} @@ 2 :> {1} @@ 3 :> {1, 2}),
      outgoing |-> (1 :> {2, 3} @@ 2 :> {3} @@ 3 :> {}),
      mailbox  |-> (1 :> {[phase |-> "up", sndr |-> 3, reply |-> "yes"]}
                    @@ 2 :> {[phase |-> "down", sndr |-> 1, val |-> 1],
                             [phase |-> "up", sndr |-> 3, reply |-> "yes"]}
                    @@ 3 :> {}) ]

(***************************************************************************)
(* TLC-generated counterexample object embedded as PostCondition. It      *)
(* records a violating behavior trace (a lasso ending in stuttering) and  *)
(* the reachable states, refuting EventuallyAlwaysAllDown.                *)
(***************************************************************************)
PostCondition ==
    [ state  |-> { <<1, CEState1>>,
                   <<2, CEState2>>,
                   <<3, CEState3>>,
                   <<4, CEState4>> },
      action |-> { << <<1, CEState1>>,
                      [name |-> "DownSource", location |-> "YoYoNoPruning"],
                      <<2, CEState2>> >>,
                   << <<2, CEState2>>,
                      [name |-> "DownOther", location |-> "YoYoNoPruning"],
                      <<3, CEState3>> >>,
                   << <<3, CEState3>>,
                      [name |-> "DownOther", location |-> "YoYoNoPruning"],
                      <<4, CEState4>> >>,
                   << <<4, CEState4>>,
                      [name |-> "Stuttering", location |-> "MCYoYoNoPruning"],
                      <<4, CEState4>> >> } ]

=============================================================================