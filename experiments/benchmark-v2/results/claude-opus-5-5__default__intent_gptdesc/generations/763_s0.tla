------------------------------ MODULE HygienicDiningPhilosophers ------------------------------
(***************************************************************************)
(* Chandy-Misra "hygienic" dining philosophers.                             *)
(*                                                                          *)
(* N philosophers 0..N-1 sit in a ring. Fork f is shared by philosopher f   *)
(* and philosopher (f+1) % N. So philosopher p uses fork p (left) and fork  *)
(* (p+N-1) % N (right).                                                     *)
(*                                                                          *)
(* Each fork has a holder and is either clean or dirty. Each edge (fork)    *)
(* also carries one request token, held by exactly one of the two           *)
(* neighbours. A pending request on fork f exists exactly when the fork     *)
(* holder also holds the request token.                                     *)
(*                                                                          *)
(* Protocol rules:                                                          *)
(*  - A hungry philosopher that holds the request token for a missing fork  *)
(*    may send the token to the neighbour that holds the fork.              *)
(*  - A holder with a pending request must grant the fork if it is dirty    *)
(*    and the holder is not eating. The fork is cleaned before it is sent.  *)
(*  - A request for a clean fork is refused, meaning deferred: the holder   *)
(*    keeps the fork until it has eaten, which makes the fork dirty.        *)
(*  - A hungry philosopher eats when it holds both forks and owes neither   *)
(*    of them, i.e. no dirty fork has a pending request. Eating dirties     *)
(*    both forks.                                                           *)
(*  - After eating, a philosopher keeps its dirty forks. It returns them    *)
(*    when a neighbour requests them.                                       *)
(*                                                                          *)
(* The initial fork placement makes the precedence graph acyclic. The       *)
(* protocol keeps it acyclic, which guarantees there is no deadlock. With   *)
(* weak fairness, the protocol also guarantees there is no starvation.      *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 2

VARIABLES state,     \* state[p] \in {"thinking","hungry","eating"}
          holder,    \* holder[f] : philosopher currently holding fork f
          clean,     \* clean[f]  : TRUE iff fork f is clean
          reqToken   \* reqToken[f] : philosopher holding the request token of fork f

vars == <<state, holder, clean, reqToken>>

Phil  == 0 .. (N - 1)
Forks == 0 .. (N - 1)

LeftFork(p)  == p
RightFork(p) == (p + N - 1) % N
ForksOf(p)   == {LeftFork(p), RightFork(p)}

\* The two philosophers adjacent to fork f
Users(f) == {f, (f + 1) % N}

\* The other philosopher sharing fork f with p
Other(f, p) == IF p = f THEN (f + 1) % N ELSE f

HoldsBoth(p) == \A f \in ForksOf(p) : holder[f] = p

\* p holds fork f and a request for it is pending
Pending(p, f) == holder[f] = p /\ reqToken[f] = p

\* p owes fork f: a request is pending and the fork is dirty
Owes(p, f) == Pending(p, f) /\ ~clean[f]

---------------------------------------------------------------------------
TypeOK ==
    /\ state    \in [Phil  -> {"thinking", "hungry", "eating"}]
    /\ holder   \in [Forks -> Phil]
    /\ clean    \in [Forks -> BOOLEAN]
    /\ reqToken \in [Forks -> Phil]

\* Initial state: all philosophers think and all forks are dirty.
\* Fork f goes to the lower-numbered of its two users, which makes the
\* precedence graph acyclic. The request token goes to the other user.
Init ==
    /\ state    = [p \in Phil |-> "thinking"]
    /\ holder   = [f \in Forks |-> IF f < N - 1 THEN f ELSE 0]
    /\ clean    = [f \in Forks |-> FALSE]
    /\ reqToken = [f \in Forks |-> Other(f, IF f < N - 1 THEN f ELSE 0)]

---------------------------------------------------------------------------
(* Actions *)

\* A thinking philosopher becomes hungry.
BecomeHungry(p) ==
    /\ state[p] = "thinking"
    /\ state' = [state EXCEPT ![p] = "hungry"]
    /\ UNCHANGED <<holder, clean, reqToken>>

\* A hungry philosopher lacks fork f and holds its request token.
\* It sends the token (the request) to the neighbour that holds the fork.
RequestFork(p, f) ==
    /\ state[p] = "hungry"
    /\ f \in ForksOf(p)
    /\ holder[f] # p
    /\ reqToken[f] = p
    /\ reqToken' = [reqToken EXCEPT ![f] = Other(f, p)]
    /\ UNCHANGED <<state, holder, clean>>

\* The holder of a dirty fork with a pending request is not eating.
\* It cleans the fork and hands it to the requester. The request token
\* stays with p, so p can later ask for the fork back.
\* A request for a clean fork is refused (deferred) because this action
\* is not enabled for it.
GrantFork(p, f) ==
    /\ f \in ForksOf(p)
    /\ Pending(p, f)
    /\ ~clean[f]
    /\ state[p] # "eating"
    /\ holder' = [holder EXCEPT ![f] = Other(f, p)]
    /\ clean'  = [clean  EXCEPT ![f] = TRUE]
    /\ UNCHANGED <<state, reqToken>>

\* A hungry philosopher holds both forks and owes neither of them.
\* It eats, and eating dirties both forks.
Eat(p) ==
    /\ state[p] = "hungry"
    /\ HoldsBoth(p)
    /\ \A f \in ForksOf(p) : ~Owes(p, f)
    /\ state' = [state EXCEPT ![p] = "eating"]
    /\ clean' = [f \in Forks |-> IF f \in ForksOf(p) THEN FALSE ELSE clean[f]]
    /\ UNCHANGED <<holder, reqToken>>

\* The philosopher finishes eating and goes back to thinking.
\* It keeps its dirty forks and returns them on request via GrantFork.
FinishEating(p) ==
    /\ state[p] = "eating"
    /\ state' = [state EXCEPT ![p] = "thinking"]
    /\ UNCHANGED <<holder, clean, reqToken>>

Next ==
    \E p \in Phil :
        \/ BecomeHungry(p)
        \/ \E f \in ForksOf(p) : RequestFork(p, f)
        \/ \E f \in ForksOf(p) : GrantFork(p, f)
        \/ Eat(p)
        \/ FinishEating(p)

\* There is no fairness on BecomeHungry, so a philosopher may think forever.
Fairness ==
    \A p \in Phil :
        /\ \A f \in ForksOf(p) : WF_vars(RequestFork(p, f))
        /\ \A f \in ForksOf(p) : WF_vars(GrantFork(p, f))
        /\ WF_vars(Eat(p))
        /\ WF_vars(FinishEating(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety properties *)

\* Every fork and every request token is owned by one of its two neighbours.
LegalOwnership ==
    /\ \A f \in Forks : holder[f]   \in Users(f)
    /\ \A f \in Forks : reqToken[f] \in Users(f)

\* An eating philosopher holds both of its forks.
EatingHoldsForks ==
    \A p \in Phil : state[p] = "eating" => HoldsBoth(p)

\* Mutual exclusion: two neighbours never eat at the same time, so no fork
\* is used by two philosophers at once.
MutualExclusion ==
    \A f \in Forks :
        ~(state[f] = "eating" /\ state[(f + 1) % N] = "eating")

\* Forks used for eating are dirty.
EatingForksDirty ==
    \A p \in Phil : state[p] = "eating" => \A f \in ForksOf(p) : ~clean[f]

\* Only hungry philosophers hold clean forks.
CleanForksHeldByHungry ==
    \A f \in Forks : clean[f] => state[holder[f]] = "hungry"

\* Precedence on edge f: the holder of a clean fork, or the non-holder of a
\* dirty fork, has priority.
Higher(f) == IF clean[f] THEN holder[f] ELSE Other(f, holder[f])

\* The precedence graph on the ring is acyclic.
\* A cycle would mean all edges are oriented the same way around the ring.
PrecedenceAcyclic ==
    /\ ~(\A f \in Forks : Higher(f) = (f + 1) % N)
    /\ ~(\A f \in Forks : Higher(f) = f)

\* There is no circular wait: it is never the case that every philosopher
\* is hungry and holds exactly one fork, all on the same side.
NoCircularWait ==
    /\ ~(\A p \in Phil : state[p] = "hungry" /\ holder[LeftFork(p)]  = p
                                            /\ holder[RightFork(p)] # p)
    /\ ~(\A p \in Phil : state[p] = "hungry" /\ holder[RightFork(p)] = p
                                            /\ holder[LeftFork(p)]  # p)

\* Absence of deadlock: some step is always possible.
DeadlockFree == ENABLED Next

\* There is no deadlock among hungry philosophers: if anyone is hungry,
\* some protocol step other than BecomeHungry is enabled.
HungryProgressPossible ==
    (\E p \in Phil : state[p] = "hungry") =>
        ENABLED (\E p \in Phil :
                    \/ \E f \in ForksOf(p) : RequestFork(p, f)
                    \/ \E f \in ForksOf(p) : GrantFork(p, f)
                    \/ Eat(p)
                    \/ FinishEating(p))

SafetyInvariant ==
    /\ TypeOK
    /\ LegalOwnership
    /\ EatingHoldsForks
    /\ MutualExclusion
    /\ EatingForksDirty
    /\ CleanForksHeldByHungry
    /\ PrecedenceAcyclic
    /\ NoCircularWait

---------------------------------------------------------------------------
(* Liveness properties *)

\* Starvation freedom: every hungry philosopher eventually eats.
StarvationFree ==
    \A p \in Phil : (state[p] = "hungry") ~> (state[p] = "eating")

\* Every eating philosopher eventually stops eating.
EatingTerminates ==
    \A p \in Phil : (state[p] = "eating") ~> (state[p] = "thinking")

\* Every pending request is eventually served or answered by a fork transfer.
RequestsServed ==
    \A f \in Forks : \A p \in Users(f) :
        (state[p] = "hungry" /\ holder[f] # p) ~> (holder[f] = p \/ state[p] = "eating")

LivenessProperty == StarvationFree /\ EatingTerminates /\ RequestsServed

---------------------------------------------------------------------------
THEOREM Spec => []SafetyInvariant
THEOREM Spec => []DeadlockFree
THEOREM Spec => []HungryProgressPossible
THEOREM Spec => LivenessProperty
=============================================================================