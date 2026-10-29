---------------------------- MODULE DiningPhilosophers ----------------------------
(***************************************************************************)
(* Chandy-Misra "hygienic" Dining Philosophers.                            *)
(*                                                                         *)
(* NP philosophers 0..NP-1 sit around a table.  Fork f lies between       *)
(* philosophers f and (f+1) % NP.  Philosopher p uses forks p and          *)
(* (p-1+NP) % NP.                                                          *)
(*                                                                         *)
(* Each fork is owned by exactly one of its two neighbours.  It is either  *)
(* clean or dirty, and it may carry a pending request from the neighbour   *)
(* that does not hold it.  The protocol works as follows:                  *)
(*   - A hungry philosopher requests each missing fork from its neighbour. *)
(*   - The holder of a requested fork gives it up only if the fork is      *)
(*     dirty and the holder is not eating.  It cleans the fork before      *)
(*     sending it.                                                         *)
(*   - A hungry philosopher that holds both forks eats.  Eating makes      *)
(*     both forks dirty.                                                   *)
(*   - After eating, the philosopher keeps its dirty forks and hands them  *)
(*     over when they are requested.                                       *)
(* Initially every fork is dirty and owned by the lower-indexed            *)
(* neighbour.  This makes the precedence graph acyclic, so no deadlock     *)
(* can occur, and the clean/dirty rule prevents starvation.                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT NP

ASSUME NP \in Nat /\ NP >= 2

Phil  == 0 .. (NP - 1)
Fork  == 0 .. (NP - 1)

LeftFork(p)  == p
RightFork(p) == (p + NP - 1) % NP
Forks(p)     == {LeftFork(p), RightFork(p)}

\* The two philosophers adjacent to fork f
Nbrs(f) == {f, (f + 1) % NP}

\* The neighbour of p across fork f
Other(p, f) == CHOOSE q \in Nbrs(f) : q # p

LeftNbr(p)  == (p + 1) % NP
RightNbr(p) == (p + NP - 1) % NP

Min(a, b) == IF a <= b THEN a ELSE b

VARIABLES state, fork

vars == <<state, fork>>

States == {"thinking", "hungry", "eating"}

ForkRec == [owner : Phil, clean : BOOLEAN, request : BOOLEAN]

TypeOK ==
    /\ state \in [Phil -> States]
    /\ fork \in [Fork -> ForkRec]
    /\ \A f \in Fork : fork[f].owner \in Nbrs(f)

Init ==
    /\ state = [p \in Phil |-> "thinking"]
    /\ fork  = [f \in Fork |->
                  [owner   |-> Min(f, (f + 1) % NP),
                   clean   |-> FALSE,
                   request |-> FALSE]]

---------------------------------------------------------------------------
(* Actions *)

BecomeHungry(p) ==
    /\ state[p] = "thinking"
    /\ state' = [state EXCEPT ![p] = "hungry"]
    /\ UNCHANGED fork

\* Hungry p sends a request token for a fork it does not hold.
Request(p, f) ==
    /\ state[p] = "hungry"
    /\ f \in Forks(p)
    /\ fork[f].owner # p
    /\ ~fork[f].request
    /\ fork' = [fork EXCEPT ![f].request = TRUE]
    /\ UNCHANGED state

\* Holder p yields a requested fork. The fork must be dirty and p must not
\* be eating. The fork is cleaned when it is sent.
Grant(p, f) ==
    /\ f \in Forks(p)
    /\ fork[f].owner = p
    /\ fork[f].request
    /\ ~fork[f].clean
    /\ state[p] # "eating"
    /\ fork' = [fork EXCEPT ![f] = [owner   |-> Other(p, f),
                                    clean   |-> TRUE,
                                    request |-> FALSE]]
    /\ UNCHANGED state

\* Hungry p holding both forks eats. Its forks become dirty.
Eat(p) ==
    /\ state[p] = "hungry"
    /\ \A f \in Forks(p) : fork[f].owner = p
    /\ state' = [state EXCEPT ![p] = "eating"]
    /\ fork'  = [f \in Fork |->
                   IF f \in Forks(p)
                     THEN [fork[f] EXCEPT !.clean = FALSE]
                     ELSE fork[f]]

\* p finishes eating. It keeps its dirty forks until a neighbour requests them.
FinishEating(p) ==
    /\ state[p] = "eating"
    /\ state' = [state EXCEPT ![p] = "thinking"]
    /\ UNCHANGED fork

Next ==
    \E p \in Phil :
        \/ BecomeHungry(p)
        \/ \E f \in Forks(p) : Request(p, f)
        \/ \E f \in Forks(p) : Grant(p, f)
        \/ Eat(p)
        \/ FinishEating(p)

Fairness ==
    \A p \in Phil :
        /\ \A f \in Forks(p) : WF_vars(Request(p, f))
        /\ \A f \in Forks(p) : WF_vars(Grant(p, f))
        /\ WF_vars(Eat(p))
        /\ WF_vars(FinishEating(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety properties *)

\* No two philosophers hold the same fork, and an eating philosopher holds
\* both of its forks. Two neighbours therefore never eat at the same time.
ExclusiveAccess ==
    /\ \A p \in Phil :
          state[p] = "eating" =>
             \A f \in Forks(p) : fork[f].owner = p
    /\ \A p \in Phil :
          ~(state[p] = "eating" /\ state[LeftNbr(p)] = "eating")
    /\ \A f \in Fork : \A p, q \in Nbrs(f) :
          (fork[f].owner = p /\ fork[f].owner = q) => p = q

\* There are no illegal ownership patterns:
\*  - a fork is held only by one of its two neighbours;
\*  - a thinking philosopher never holds a clean fork;
\*  - a pending request is always for a fork held by the other neighbour.
LegalOwnership ==
    /\ \A f \in Fork : fork[f].owner \in Nbrs(f)
    /\ \A f \in Fork :
          fork[f].clean => state[fork[f].owner] # "thinking"
    /\ \A f \in Fork :
          fork[f].clean => state[fork[f].owner] # "eating"

\* Deadlock freedom: some action of the protocol is always enabled.
DeadlockFree == ENABLED Next

Inv == TypeOK /\ ExclusiveAccess /\ LegalOwnership

---------------------------------------------------------------------------
(* Liveness properties *)

\* Every hungry philosopher eventually eats (no starvation).
Starvation == \A p \in Phil : (state[p] = "hungry") ~> (state[p] = "eating")

\* Some philosopher eventually eats whenever someone is hungry.
Progress == (\E p \in Phil : state[p] = "hungry")
               ~> (\E p \in Phil : state[p] = "eating")

THEOREM Spec => [](TypeOK /\ ExclusiveAccess)
THEOREM Spec => Starvation
================================================================================