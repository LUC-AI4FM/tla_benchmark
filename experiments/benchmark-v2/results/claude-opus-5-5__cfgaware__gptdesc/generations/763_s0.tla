------------------------- MODULE APADiningPhilosophers -------------------------
(***************************************************************************)
(* Apalache-oriented wrapper for the Dining Philosophers specification.    *)
(* The type annotations live here, so the underlying specification stays   *)
(* free of tool-specific details. The DiningPhilosophers definitions are   *)
(* inlined so that this module is self-contained.                          *)
(* The model is the hygienic (Chandy-Misra) solution.                      *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
    \* @type: Int;
    NP

VARIABLES
    \* @type: Int -> {holder: Int, clean: Bool};
    fork,
    \* @type: Int -> Bool;
    hungry

vars == <<fork, hungry>>

Philosophers == 0..(NP - 1)

LeftFork(p)  == p
RightFork(p) == (p + 1) % NP

LeftPhilosopher(p)  == (p - 1) % NP
RightPhilosopher(p) == (p + 1) % NP

\* The two philosophers that share fork f
Sharers(f) == {f, (f - 1) % NP}

IsHoldingBothForks(p) ==
    /\ fork[LeftFork(p)].holder = p
    /\ fork[RightFork(p)].holder = p

BothForksAreClean(p) ==
    /\ fork[LeftFork(p)].clean
    /\ fork[RightFork(p)].clean

CanEat(p) == IsHoldingBothForks(p) /\ BothForksAreClean(p)

TypeOK ==
    /\ fork \in [Philosophers -> [holder : Philosophers, clean : BOOLEAN]]
    /\ hungry \in [Philosophers -> BOOLEAN]

Init ==
    /\ fork = [f \in Philosophers |->
                 IF f = NP - 1
                 THEN [holder |-> 0, clean |-> FALSE]
                 ELSE [holder |-> f, clean |-> FALSE]]
    /\ hungry \in [Philosophers -> BOOLEAN]

\* A philosopher who is not hungry becomes hungry.
BecomeHungry(p) ==
    /\ ~hungry[p]
    /\ hungry' = [hungry EXCEPT ![p] = TRUE]
    /\ UNCHANGED fork

\* A hungry philosopher holding both clean forks eats, dirtying the forks.
Eat(p) ==
    /\ hungry[p]
    /\ CanEat(p)
    /\ hungry' = [hungry EXCEPT ![p] = FALSE]
    /\ fork' = [fork EXCEPT ![LeftFork(p)].clean = FALSE,
                            ![RightFork(p)].clean = FALSE]

\* A philosopher holding a dirty fork hands it, cleaned, to a hungry neighbor.
GiveFork(p, f) ==
    /\ fork[f].holder = p
    /\ ~fork[f].clean
    /\ \E q \in Sharers(f) \ {p} :
          /\ hungry[q]
          /\ fork' = [fork EXCEPT ![f] = [holder |-> q, clean |-> TRUE]]
    /\ UNCHANGED hungry

Next ==
    \E p \in Philosophers :
        \/ BecomeHungry(p)
        \/ Eat(p)
        \/ \E f \in {LeftFork(p), RightFork(p)} : GiveFork(p, f)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

ExclusiveAccess ==
    \A p \in Philosophers :
        CanEat(p) =>
            /\ (LeftPhilosopher(p) # p => ~CanEat(LeftPhilosopher(p)))
            /\ (RightPhilosopher(p) # p => ~CanEat(RightPhilosopher(p)))

=============================================================================