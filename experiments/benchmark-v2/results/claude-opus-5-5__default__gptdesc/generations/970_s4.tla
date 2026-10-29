------------------------------- MODULE TLCMC -------------------------------
(***************************************************************************)
(* A TLC-like reachability model checker.  It explores a state graph in    *)
(* breadth-first order.  The parameter K selects the exploration mode:     *)
(*   K = 1 : strict BFS.  The head of the queue is always dequeued.        *)
(*   K > 1 : non-strict BFS.  Any of the first K queue entries may be      *)
(*           dequeued, which approximates K concurrent workers.            *)
(* When the checker finds a violation state, it rebuilds a counterexample  *)
(* from the recorded predecessor relation.                                 *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

---------------------------- MODULE MCReachability ---------------------------
(***************************************************************************)
(* Abstract reachability.  Each step marks as reached one state that is    *)
(* either initial or a successor of an already reached state.             *)
(***************************************************************************)
CONSTANT Graph
VARIABLE reached

RInit == reached = {}

RSucc(R) == {t \in Graph.states : \E s \in R : <<s, t>> \in Graph.actions}

RNext == \E t \in (Graph.initials \cup RSucc(reached)) :
            reached' = reached \cup {t}

RSpec == RInit /\ [][RNext]_reached
==============================================================================