------------------------- MODULE DiningPhilosophers_Apalache -------------------------
(***************************************************************************)
(* Apalache-compatible, type-annotated Dining Philosophers specification   *)
(* (Chandy-Misra "hygienic" style). Self-contained so that it parses on    *)
(* its own. Fairness is omitted (safety checking only).                    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    \* @type: Int;
    NP

VARIABLES
    \* @type: Int -> { holder: Int, clean: Bool };
    forks,
    \* @type: Int -> Str;
    pc,
    \* @type: Int -> Bool;
    hungry

vars == <<forks, pc, hungry>>

Philosophers == 0 .. (NP - 1)
Forks == 0 .. (NP - 1)

\* Fork f lies between philosopher f and philosopher (f + 1) % NP.
\* @type: (Int) => Int;
LeftFork(p) == p
\* @type: (Int) => Int;
RightFork(p) == (p + NP - 1) % NP

\* @type: (Int) => Set(Int);
ForksOf(p) == {LeftFork(p), RightFork(p)}

\* @type: (Int) => Set(Int);
Sharers(f) == {f, (f + 1) % NP}

\* @type: (Int) => Int;
RightNeighbor(p) == (p + 1) % NP

\* @type: (Int, Int) => Int;
Min(a, b) == IF a <= b THEN a ELSE b

States == {"Think", "Hungry", "Eat"}

ForkRecords == [holder : Philosophers, clean : BOOLEAN]

-----------------------------------------------------------------------------

Init ==
    /\ forks = [f \in Forks |-> [holder |-> Min(f, (f + 1) % NP), clean |-> FALSE]]
    /\ pc = [p \in Philosophers |-> "Think"]
    /\ hungry = [p \in Philosophers |-> FALSE]

\* A thinking philosopher becomes hungry.
\* @type: (Int) => Bool;
BecomeHungry(p) ==
    /\ pc[p] = "Think"
    /\ pc' = [pc EXCEPT ![p] = "Hungry"]
    /\ hungry' = [hungry EXCEPT ![p] = TRUE]
    /\ UNCHANGED forks

\* A hungry philosopher obtains a dirty fork from a neighbor that is not
\* eating; the fork is cleaned when it is handed over.
\* @type: (Int, Int) => Bool;
AcquireFork(p, f) ==
    /\ pc[p] = "Hungry"
    /\ f \in ForksOf(p)
    /\ forks[f].holder # p
    /\ ~forks[f].clean
    /\ pc[forks[f].holder] # "Eat"
    /\ forks' = [forks EXCEPT ![f] = [holder |-> p, clean |-> TRUE]]
    /\ UNCHANGED <<pc, hungry>>

\* A hungry philosopher holding both forks starts eating.
\* @type: (Int) => Bool;
Eat(p) ==
    /\ pc[p] = "Hungry"
    /\ \A f \in ForksOf(p) : forks[f].holder = p
    /\ pc' = [pc EXCEPT ![p] = "Eat"]
    /\ hungry' = [hungry EXCEPT ![p] = FALSE]
    /\ UNCHANGED forks

\* A philosopher finishes eating; its forks become dirty.
\* @type: (Int) => Bool;
FinishEating(p) ==
    /\ pc[p] = "Eat"
    /\ pc' = [pc EXCEPT ![p] = "Think"]
    /\ forks' = [f \in Forks |->
                    IF f \in ForksOf(p)
                    THEN [holder |-> forks[f].holder, clean |-> FALSE]
                    ELSE forks[f]]
    /\ UNCHANGED hungry

Next ==
    \E p \in Philosophers :
        \/ BecomeHungry(p)
        \/ \E f \in Forks : AcquireFork(p, f)
        \/ Eat(p)
        \/ FinishEating(p)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeOK ==
    /\ forks \in [Forks -> ForkRecords]
    /\ pc \in [Philosophers -> States]
    /\ hungry \in [Philosophers -> BOOLEAN]

\* No two adjacent philosophers are simultaneously using the fork between them.
ExclusiveAccess ==
    \A p \in Philosophers :
        (p # RightNeighbor(p)) =>
            ~(pc[p] = "Eat" /\ pc[RightNeighbor(p)] = "Eat")

=============================================================================