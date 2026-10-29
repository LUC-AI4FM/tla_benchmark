------------------------------ MODULE MCYoYoNoPruning ------------------------------
(***************************************************************************)
(* Model-checking wrapper for the YoYo leader-election algorithm without   *)
(* pruning. The graph is fixed here, and the YoYoNoPruning module is       *)
(* instantiated without substitutions. The algorithm's transition relation *)
(* comes from that module. This module states the liveness-style           *)
(* postcondition that eventually every node stays in the "down" phase. It  *)
(* also embeds a TLC-generated counterexample as PostCondition.            *)
(***************************************************************************)
EXTENDS TLC, Naturals, FiniteSets, Sequences

(***************************************************************************)
(* Small graph used for model checking.                                    *)
(***************************************************************************)
Nodes == {1, 2, 3}
Edges == {{1, 2}, {2, 3}}

(***************************************************************************)
(* Larger alternative graph (kept for reference):                          *)
(*                                                                         *)
(* Nodes == 1 .. 10                                                        *)
(* Edges == {{1,2}, {1,9}, {2,3}, {2,10}, {3,4}, {3,6}, {4,5}, {4,8},     *)
(*           {5,6}, {6,7}, {7,8}, {7,9}, {8,10}, {9,10}}                  *)
(***************************************************************************)

VARIABLES phase, incoming, outgoing, mailbox

vars == <<phase, incoming, outgoing, mailbox>>

YY == INSTANCE YoYoNoPruning

Init == YY!Init
Next == YY!Next
Spec == YY!Spec

(* Fairness so that the liveness property can be checked meaningfully. *)
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* Safety: type correctness is taken from the instantiated module.         *)
(***************************************************************************)
TypeOK == YY!TypeOK

(***************************************************************************)
(* Liveness-style postcondition: eventually all nodes remain permanently   *)
(* in the "down" phase.                                                    *)
(***************************************************************************)
AllDown == \A n \in Nodes : phase[n] = "down"

EventuallyAlwaysDown == <>[](AllDown)

(***************************************************************************)
(* TLC-generated counterexample showing a behavior that violates the      *)
(* property above. The trace starts in the initial state, then reaches a   *)
(* state where node 1 has left the "down" phase.                           *)
(***************************************************************************)
CEState1 ==
    [ phase    |-> (1 :> "down") @@ (2 :> "down") @@ (3 :> "down"),
      incoming |-> (1 :> {})     @@ (2 :> {1})    @@ (3 :> {2}),
      outgoing |-> (1 :> {2})    @@ (2 :> {3})    @@ (3 :> {}),
      mailbox  |-> (1 :> {})     @@ (2 :> {})     @@ (3 :> {}) ]

CEState2 ==
    [ phase    |-> (1 :> "up")   @@ (2 :> "down") @@ (3 :> "down"),
      incoming |-> (1 :> {})     @@ (2 :> {1})    @@ (3 :> {2}),
      outgoing |-> (1 :> {2})    @@ (2 :> {3})    @@ (3 :> {}),
      mailbox  |-> (1 :> {})
                   @@ (2 :> {[phase |-> "down", sndr |-> 1, val |-> 1]})
                   @@ (3 :> {}) ]

CEState3 ==
    [ phase    |-> (1 :> "up")   @@ (2 :> "up")   @@ (3 :> "down"),
      incoming |-> (1 :> {})     @@ (2 :> {1})    @@ (3 :> {2}),
      outgoing |-> (1 :> {2})    @@ (2 :> {3})    @@ (3 :> {}),
      mailbox  |-> (1 :> {})
                   @@ (2 :> {})
                   @@ (3 :> {[phase |-> "down", sndr |-> 2, val |-> 1]}) ]

PostCondition ==
    [ state  |-> { <<1, CEState1>>, <<2, CEState2>>, <<3, CEState3>> },
      action |-> { << <<1, CEState1>>, [name |-> "DownSource"],   <<2, CEState2>> >>,
                   << <<2, CEState2>>, [name |-> "DownOther"],    <<3, CEState3>> >>,
                   << <<3, CEState3>>, [name |-> "Stuttering"],   <<3, CEState3>> >> } ]

=============================================================================