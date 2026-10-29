------------------------------- MODULE MCYoYoNoPruning -------------------------------
(***************************************************************************)
(* Model-checking wrapper for the YoYoNoPruning specification.             *)
(* It fixes a small graph, instantiates YoYoNoPruning without              *)
(* substitutions, states a liveness-style property over the imported       *)
(* state variables, and embeds a TLC-generated counterexample object as    *)
(* PostCondition.                                                          *)
(***************************************************************************)
EXTENDS TLC, Naturals, FiniteSets

(***************************************************************************)
(* Fixed small graph used for model checking.                              *)
(***************************************************************************)
Nodes == {1, 2, 3}
Edges == {{1, 2}, {2, 3}}

(***************************************************************************)
(* A larger alternative graph (disabled):                                  *)
(*                                                                         *)
(* Nodes == {2, 3, 4, 5, 7, 9, 10, 11, 12, 13}                             *)
(* Edges == { {2,4}, {2,7}, {2,10}, {3,4}, {3,5}, {3,11},                  *)
(*            {4,7}, {4,11}, {5,9}, {5,12}, {7,13}, {9,12},                *)
(*            {10,13}, {11,12} }                                           *)
(***************************************************************************)

VARIABLES phase, incoming, outgoing, mailbox

vars == <<phase, incoming, outgoing, mailbox>>

(***************************************************************************)
(* Instantiate YoYoNoPruning without substitutions: the constants Nodes    *)
(* and Edges and the state variables above are bound by name.              *)
(***************************************************************************)
YY == INSTANCE YoYoNoPruning

Init == YY!Init
Next == YY!Next
Spec == YY!Spec

(***************************************************************************)
(* Liveness-style property: eventually all nodes remain permanently in     *)
(* the "down" phase.                                                       *)
(***************************************************************************)
Liveness == <>[](\A n \in Nodes : phase[n] = "down")

(***************************************************************************)
(* TLC-generated counterexample object recorded as PostCondition, showing  *)
(* a violating behavior trace (states and actions) on the fixed graph.     *)
(***************************************************************************)
S1 == [ phase    |-> (1 :> "down" @@ 2 :> "down" @@ 3 :> "down"),
        incoming |-> (1 :> {} @@ 2 :> {1} @@ 3 :> {2}),
        outgoing |-> (1 :> {2} @@ 2 :> {3} @@ 3 :> {}),
        mailbox  |-> (1 :> {} @@ 2 :> {} @@ 3 :> {}) ]

S2 == [ phase    |-> (1 :> "up" @@ 2 :> "down" @@ 3 :> "down"),
        incoming |-> (1 :> {} @@ 2 :> {1} @@ 3 :> {2}),
        outgoing |-> (1 :> {2} @@ 2 :> {3} @@ 3 :> {}),
        mailbox  |-> (1 :> {} @@
                      2 :> {[phase |-> "down", sndr |-> 1, val |-> 1]} @@
                      3 :> {}) ]

S3 == [ phase    |-> (1 :> "up" @@ 2 :> "up" @@ 3 :> "down"),
        incoming |-> (1 :> {} @@ 2 :> {1} @@ 3 :> {2}),
        outgoing |-> (1 :> {2} @@ 2 :> {3} @@ 3 :> {}),
        mailbox  |-> (1 :> {} @@
                      2 :> {[phase |-> "down", sndr |-> 1, val |-> 1]} @@
                      3 :> {[phase |-> "down", sndr |-> 2, val |-> 1]}) ]

S4 == [ phase    |-> (1 :> "up" @@ 2 :> "up" @@ 3 :> "up"),
        incoming |-> (1 :> {} @@ 2 :> {1} @@ 3 :> {2}),
        outgoing |-> (1 :> {2} @@ 2 :> {3} @@ 3 :> {}),
        mailbox  |-> (1 :> {} @@
                      2 :> {[phase |-> "down", sndr |-> 1, val |-> 1],
                            [phase |-> "up", sndr |-> 3, reply |-> "yes"]} @@
                      3 :> {[phase |-> "down", sndr |-> 2, val |-> 1]}) ]

PostCondition ==
  [ state  |-> { <<1, S1>>, <<2, S2>>, <<3, S3>>, <<4, S4>> },
    action |-> { << <<1, S1>>, [name |-> "DownSource", node |-> 1], <<2, S2>> >>,
                 << <<2, S2>>, [name |-> "DownOther",  node |-> 2], <<3, S3>> >>,
                 << <<3, S3>>, [name |-> "DownSink",   node |-> 3], <<4, S4>> >>,
                 << <<4, S4>>, [name |-> "Stuttering", node |-> 0], <<4, S4>> >> } ]

=====================================================================================