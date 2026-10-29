---------------------------- MODULE TLCMC ----------------------------
(***************************************************************************)
(* A TLC-like reachability model checker.  It explores a state graph in    *)
(* breadth-first order.  The parameter K controls the exploration order:   *)
(* K = 1 is strict BFS.  K > 1 is a degraded, non-strict BFS: any of the   *)
(* first K pending states may be dequeued, which approximates K workers.   *)
(*                                                                         *)
(* The state graph is a record with fields states, initials and actions.   *)
(* The checker tracks these values:                                        *)
(*   S       explored states                                               *)
(*   C       predecessor map                                               *)
(*   L       BFS levels                                                    *)
(*   Q       queue of pending states                                       *)
(* When it finds a violation, it rebuilds a counterexample from C.         *)
(*                                                                         *)
(* The definitions below are the TLA+ translation of the PlusCal           *)
(* algorithm.                                                              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

---------------------------- MODULE MCReachability ----------------------------
(***************************************************************************)
(* The abstract reachability specification.  The set of visited states     *)
(* only grows, and only by initial states or successors of states it       *)
(* already holds.  On termination, the result is either no counterexample  *)
(* or a valid path that runs from an initial state to a violation state.   *)
(***************************************************************************)
CONSTANTS RG, RV
VARIABLES visited, cex, finished

rvars == <<visited, cex, finished>>

RSucc(X) == { t \in RG.states : \E s \in X : <<s, t>> \in RG.actions }

RIsCex(p) ==
    /\ Len(p) >= 1
    /\ p[1] \in RG.initials
    /\ \A j \in 1..(Len(p) - 1) : <<p[j], p[j + 1]>> \in RG.actions
    /\ p[Len(p)] \in RV

RInit ==
    /\ visited \subseteq RG.initials
    /\ cex = << >>
    /\ finished = FALSE

RNext ==
    /\ ~finished
    /\ \E N \in SUBSET (RG.initials \cup RSucc(visited)) :
           visited' = visited \cup N
    /\ \/ /\ finished' = FALSE
          /\ cex' = << >>
       \/ /\ finished' = TRUE
          /\ \/ cex' = << >>
             \/ RIsCex(cex')

RSpec == RInit /\ [][RNext]_rvars
================================================================================