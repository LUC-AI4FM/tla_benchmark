------------------------- MODULE DiningPhilosophers -------------------------
(***************************************************************************)
(* Dining philosophers with a fork-passing protocol in the style of        *)
(* Chandy-Misra (clean/dirty forks with request tokens).                   *)
(*                                                                         *)
(* Philosophers are 0..N-1 around a round table. Fork f lies between       *)
(* philosopher f and philosopher (f+1) % N. Philosopher p therefore uses   *)
(* fork p and fork (p-1) % N.                                              *)
(*                                                                         *)
(* Protocol rules:                                                         *)
(*  - A hungry philosopher may request a fork it does not hold.            *)
(*  - A holder must hand over a requested fork when it is dirty and the    *)
(*    holder is not eating. A thinking holder may always hand it over.     *)
(*    A handed-over fork arrives clean.                                    *)
(*  - A hungry philosopher eats when it holds both forks and neither fork  *)
(*    is both dirty and requested.                                         *)
(*  - When a philosopher finishes eating, both of its forks become dirty.  *)
(*  - Initially all forks are dirty and are held by the lower-numbered     *)
(*    neighbour. This makes the precedence graph acyclic.                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 2

Phil  == 0 .. (N - 1)
Forks == 0 .. (N - 1)

\* The two philosophers adjacent to fork f
Ends(f) == { f, (f + 1) % N }

\* The two forks adjacent to philosopher p
ForksOf(p) == { p, (p + N - 1) % N }

\* The other philosopher sharing fork f with p
Other(f, p) == CHOOSE q \in Ends(f) : q /= p

\* Right neighbour of p (shares fork p)
RightNbr(p) == (p + 1) % N

States == {"thinking", "hungry", "eating"}

VARIABLES
    state,    \* state[p]  : philosopher state
    holder,   \* holder[f] : philosopher currently holding fork f
    clean,    \* clean[f]  : TRUE iff fork f is clean
    reqd      \* reqd[f]   : TRUE iff the non-holder has requested fork f

vars == << state, holder, clean, reqd >>

-----------------------------------------------------------------------------
TypeOK ==
    /\ state  \in [Phil  -> States]
    /\ holder \in [Forks -> Phil]
    /\ clean  \in [Forks -> BOOLEAN]
    /\ reqd   \in [Forks -> BOOLEAN]

Init ==
    /\ state  = [p \in Phil |-> "thinking"]
    /\ holder = [f \in Forks |-> IF f < (f + 1) % N THEN f ELSE (f + 1) % N]
    /\ clean  = [f \in Forks |-> FALSE]
    /\ reqd   = [f \in Forks |-> FALSE]

-----------------------------------------------------------------------------
(* Actions *)

\* A thinking philosopher becomes hungry.
BecomeHungry(p) ==
    /\ state[p] = "thinking"
    /\ state' = [state EXCEPT ![p] = "hungry"]
    /\ UNCHANGED << holder, clean, reqd >>

\* A hungry philosopher requests an adjacent fork it does not hold.
\* This sends the request token to the neighbour.
RequestFork(p, f) ==
    /\ f \in ForksOf(p)
    /\ state[p] = "hungry"
    /\ holder[f] /= p
    /\ ~reqd[f]
    /\ reqd' = [reqd EXCEPT ![f] = TRUE]
    /\ UNCHANGED << state, holder, clean >>

\* The holder hands a requested fork to its neighbour.
\* The fork is cleaned when it is passed.
ReleaseFork(p, f) ==
    /\ f \in ForksOf(p)
    /\ holder[f] = p
    /\ reqd[f]
    /\ state[p] /= "eating"
    /\ (~clean[f] \/ state[p] = "thinking")
    /\ holder' = [holder EXCEPT ![f] = Other(f, p)]
    /\ clean'  = [clean  EXCEPT ![f] = TRUE]
    /\ reqd'   = [reqd   EXCEPT ![f] = FALSE]
    /\ UNCHANGED state

\* A fork permits eating unless it is dirty and requested by the neighbour.
ForkPermitsEating(f) == clean[f] \/ ~reqd[f]

\* A hungry philosopher holding both usable forks starts eating.
Eat(p) ==
    /\ state[p] = "hungry"
    /\ \A f \in ForksOf(p) : holder[f] = p /\ ForkPermitsEating(f)
    /\ state' = [state EXCEPT ![p] = "eating"]
    /\ UNCHANGED << holder, clean, reqd >>

\* A philosopher finishes eating. Both of its forks become dirty.
DoneEating(p) ==
    /\ state[p] = "eating"
    /\ state' = [state EXCEPT ![p] = "thinking"]
    /\ clean' = [f \in Forks |-> IF f \in ForksOf(p) THEN FALSE ELSE clean[f]]
    /\ UNCHANGED << holder, reqd >>

PhilNext(p) ==
    \/ BecomeHungry(p)
    \/ \E f \in ForksOf(p) : RequestFork(p, f)
    \/ \E f \in ForksOf(p) : ReleaseFork(p, f)
    \/ Eat(p)
    \/ DoneEating(p)

Next == \E p \in Phil : PhilNext(p)

\* Fairness for philosopher processes. Thinking philosophers are never forced
\* to become hungry. Every protocol step is weakly fair, eating is strongly
\* fair, and eating philosophers eventually stop eating.
Fairness ==
    \A p \in Phil :
        /\ \A f \in ForksOf(p) : WF_vars(RequestFork(p, f))
        /\ \A f \in ForksOf(p) : WF_vars(ReleaseFork(p, f))
        /\ SF_vars(Eat(p))
        /\ WF_vars(DoneEating(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties and invariants *)

\* Each fork is held by exactly one of its two adjacent philosophers.
ForkHeldByNeighbour ==
    \A f \in Forks : holder[f] \in Ends(f)

\* An eating philosopher holds both of its forks.
EatingHoldsForks ==
    \A p \in Phil : state[p] = "eating" => \A f \in ForksOf(p) : holder[f] = p

\* No two neighbouring philosophers eat at the same time.
MutualExclusion ==
    \A p \in Phil : ~(state[p] = "eating" /\ state[RightNbr(p)] = "eating")

\* A pending request is only meaningful for a hungry non-holder.
RequestWellFormed ==
    \A f \in Forks : reqd[f] => state[Other(f, holder[f])] = "hungry"

Invariant ==
    /\ TypeOK
    /\ ForkHeldByNeighbour
    /\ EatingHoldsForks
    /\ MutualExclusion

SafetyProperty == []MutualExclusion

InvariantProperty == [](TypeOK /\ ForkHeldByNeighbour)

-----------------------------------------------------------------------------
(* Liveness and progress *)

\* Every hungry philosopher eventually eats (no starvation).
NoStarvation ==
    \A p \in Phil : (state[p] = "hungry") ~> (state[p] = "eating")

\* The system can always take a step (no global deadlock).
DeadlockFreedom == [](ENABLED Next)

\* Some philosopher eventually eats whenever someone is hungry.
Progress ==
    (\E p \in Phil : state[p] = "hungry") ~> (\E p \in Phil : state[p] = "eating")

-----------------------------------------------------------------------------
THEOREM Spec => []Invariant
THEOREM Spec => SafetyProperty
THEOREM Spec => InvariantProperty
THEOREM Spec => NoStarvation
THEOREM Spec => DeadlockFreedom
THEOREM Spec => Progress
=============================================================================