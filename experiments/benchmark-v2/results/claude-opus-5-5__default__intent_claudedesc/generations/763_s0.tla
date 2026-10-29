-------------------------- MODULE DiningPhilosophersChandyMisra --------------------------
(***************************************************************************)
(* Dining Philosophers, Chandy-Misra hygienic solution.                     *)
(*                                                                         *)
(* N philosophers 0..N-1 sit in a circle. Fork f lies between philosopher   *)
(* f and philosopher (f+1) % N. So philosopher p uses fork p (shared with   *)
(* its right neighbour) and fork (p-1) % N (shared with its left            *)
(* neighbour).                                                             *)
(*                                                                         *)
(* Each fork has a holder, a clean/dirty flag, and a request token. The     *)
(* request token is always held by one of the fork's two neighbours.        *)
(*  - A hungry philosopher that lacks a fork, but holds its request token,  *)
(*    sends the token to the fork holder. This is a request.                *)
(*  - A philosopher that holds both a fork and its request token has a      *)
(*    pending request. If the fork is dirty and the philosopher is not      *)
(*    eating, it must clean the fork and hand it over.                      *)
(*  - A hungry philosopher eats when it holds both forks, unless it has a   *)
(*    pending request for a dirty fork, which it must yield first.          *)
(*  - When a philosopher finishes eating, both its forks become dirty.      *)
(* Initially all forks are dirty. Each fork is held by the lower-numbered   *)
(* neighbour, so the precedence graph is acyclic.                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 2

Phils == 0 .. (N - 1)
Forks == 0 .. (N - 1)

\* Neighbours
RightNbr(p) == (p + 1) % N
LeftNbr(p)  == (p + N - 1) % N

\* The forks of philosopher p
RightFork(p) == p
LeftFork(p)  == (p + N - 1) % N
ForksOf(p)   == {LeftFork(p), RightFork(p)}

\* The two philosophers that share fork f
Users(f) == {f, (f + 1) % N}

\* The other philosopher sharing fork f with p
Other(f, p) == IF p = f THEN (f + 1) % N ELSE f

Min(a, b) == IF a <= b THEN a ELSE b

VARIABLES
    state,     \* state[p] \in {"thinking", "hungry", "eating"}
    holder,    \* holder[f]: philosopher currently holding fork f
    clean,     \* clean[f]: TRUE iff fork f is clean
    reqToken   \* reqToken[f]: philosopher holding the request token for fork f

vars == <<state, holder, clean, reqToken>>

States == {"thinking", "hungry", "eating"}

TypeOK ==
    /\ state    \in [Phils -> States]
    /\ holder   \in [Forks -> Phils]
    /\ clean    \in [Forks -> BOOLEAN]
    /\ reqToken \in [Forks -> Phils]
    /\ \A f \in Forks : holder[f] \in Users(f) /\ reqToken[f] \in Users(f)

Init ==
    /\ state    = [p \in Phils |-> "thinking"]
    /\ holder   = [f \in Forks |-> Min(f, (f + 1) % N)]
    /\ clean    = [f \in Forks |-> FALSE]
    /\ reqToken = [f \in Forks |-> Other(f, Min(f, (f + 1) % N))]

HoldsFork(p, f) == holder[f] = p

\* p holds fork f and also holds its request token: the neighbour wants it
PendingRequest(p, f) == HoldsFork(p, f) /\ reqToken[f] = p

-----------------------------------------------------------------------------
(* Actions *)

\* A thinking philosopher becomes hungry
BecomeHungry(p) ==
    /\ state[p] = "thinking"
    /\ state' = [state EXCEPT ![p] = "hungry"]
    /\ UNCHANGED <<holder, clean, reqToken>>

\* A hungry philosopher lacking fork f requests it by sending the request token
RequestFork(p, f) ==
    /\ f \in ForksOf(p)
    /\ state[p] = "hungry"
    /\ ~HoldsFork(p, f)
    /\ reqToken[f] = p
    /\ reqToken' = [reqToken EXCEPT ![f] = Other(f, p)]
    /\ UNCHANGED <<state, holder, clean>>

\* A non-eating philosopher holding a requested dirty fork cleans it and sends it
ReleaseFork(p, f) ==
    /\ f \in ForksOf(p)
    /\ PendingRequest(p, f)
    /\ ~clean[f]
    /\ state[p] # "eating"
    /\ holder' = [holder EXCEPT ![f] = Other(f, p)]
    /\ clean'  = [clean  EXCEPT ![f] = TRUE]
    /\ UNCHANGED <<state, reqToken>>

\* A hungry philosopher holding both forks eats, unless it owes a dirty fork
Eat(p) ==
    /\ state[p] = "hungry"
    /\ \A f \in ForksOf(p) : HoldsFork(p, f)
    /\ \A f \in ForksOf(p) : ~(PendingRequest(p, f) /\ ~clean[f])
    /\ state' = [state EXCEPT ![p] = "eating"]
    /\ UNCHANGED <<holder, clean, reqToken>>

\* An eating philosopher finishes. Its forks become dirty and it thinks again.
\* The forks stay with p until a neighbour requests them.
FinishEating(p) ==
    /\ state[p] = "eating"
    /\ state' = [state EXCEPT ![p] = "thinking"]
    /\ clean' = [f \in Forks |-> IF f \in ForksOf(p) THEN FALSE ELSE clean[f]]
    /\ UNCHANGED <<holder, reqToken>>

Next ==
    \E p \in Phils :
        \/ BecomeHungry(p)
        \/ \E f \in ForksOf(p) : RequestFork(p, f)
        \/ \E f \in ForksOf(p) : ReleaseFork(p, f)
        \/ Eat(p)
        \/ FinishEating(p)

\* Fairness: philosophers need not become hungry. Every other step of the
\* protocol, including finishing a meal, is weakly fair.
Fairness ==
    \A p \in Phils :
        /\ \A f \in ForksOf(p) : WF_vars(RequestFork(p, f))
        /\ \A f \in ForksOf(p) : WF_vars(ReleaseFork(p, f))
        /\ WF_vars(Eat(p))
        /\ WF_vars(FinishEating(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* Mutual exclusion: adjacent philosophers never eat at the same time
MutualExclusion ==
    \A p \in Phils :
        (state[p] = "eating" /\ RightNbr(p) # p) => state[RightNbr(p)] # "eating"

\* An eating philosopher holds both of its forks
EatingHoldsForks ==
    \A p \in Phils : state[p] = "eating" => \A f \in ForksOf(p) : HoldsFork(p, f)

\* Hygiene: a clean fork is only ever held by a hungry philosopher
CleanForksHeldByHungry ==
    \A f \in Forks : clean[f] => state[holder[f]] = "hungry"

\* Deadlock freedom: whenever someone is hungry, some protocol step is enabled
\* (someone is eating, or some request, release or eat step can occur)
DeadlockFreedom ==
    (\E p \in Phils : state[p] = "hungry") =>
        \E p \in Phils :
            \/ state[p] = "eating"
            \/ ENABLED Eat(p)
            \/ \E f \in ForksOf(p) : ENABLED RequestFork(p, f)
            \/ \E f \in ForksOf(p) : ENABLED ReleaseFork(p, f)

Invariants ==
    /\ TypeOK
    /\ MutualExclusion
    /\ EatingHoldsForks
    /\ CleanForksHeldByHungry
    /\ DeadlockFreedom

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Progress: if someone is hungry, eventually someone eats
Progress ==
    (\E p \in Phils : state[p] = "hungry") ~> (\E p \in Phils : state[p] = "eating")

\* Starvation freedom: every hungry philosopher eventually eats
StarvationFreedom ==
    \A p \in Phils : (state[p] = "hungry") ~> (state[p] = "eating")

THEOREM Spec => []Invariants
THEOREM Spec => Progress /\ StarvationFreedom
=============================================================================