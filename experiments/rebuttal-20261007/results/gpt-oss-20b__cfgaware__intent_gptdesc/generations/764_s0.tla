------------------------------ MODULE DiningPhilosophers ------------------------------
EXTENDS Naturals, Sequences

CONSTANT N \* number of philosophers
\* 1 .. N

(* Types *)
PhilId == 1 .. N
ForkId == 1 .. N
State   == {"Thinking", "Hungry", "Eating"}
FState  == {"Clean", "Dirty"}

VARIABLES forkOwner, forkState, philState

(* Helper functions *)
LeftFork(p)  == ((p + N - 2) % N) + 1
RightFork(p) == (p % N) + 1
Adjacent(p,q) == (q = LeftFork(p)) \/ (q = RightFork(p))

Init ==
    /\ forkOwner \in [ForkId -> PhilId]
    /\ forkState \in [ForkId -> FState]
    /\ philState \in [PhilId -> State]
    /\ \A f \in ForkId: forkOwner[f] = 0
    /\ \A f \in ForkId: forkState[f] = "Clean"
    /\ \A p \in PhilId: philState[p] = "Thinking"

Request(p) ==
    /\ philState[p] = "Thinking"
    /\ philState' = [philState EXCEPT ![p] = "Hungry"]
    /\ UNCHANGED <<forkOwner, forkState>>

AcquireForks(p) ==
    /\ philState[p] = "Hungry"
    /\ forkOwner[LeftFork(p)]  = 0
    /\ forkOwner[RightFork(p)] = 0
    /\ forkOwner' = [forkOwner EXCEPT
                      ![LeftFork(p)]  = p,
                      ![RightFork(p)] = p]
    /\ UNCHANGED <<philState, forkState>>

Eat(p) ==
    /\ philState[p] = "Hungry"
    /\ forkOwner[LeftFork(p)]  = p
    /\ forkOwner[RightFork(p)] = p
    /\ philState' = [philState EXCEPT ![p] = "Eating"]
    /\ UNCHANGED <<forkOwner, forkState>>

FinishEat(p) ==
    /\ philState[p] = "Eating"
    /\ philState' = [philState EXCEPT ![p] = "Thinking"]
    /\ forkOwner' = [forkOwner EXCEPT
                      ![LeftFork(p)]  = 0,
                      ![RightFork(p)] = 0]
    /\ UNCHANGED <<forkState>>

Next ==
    \/ \E p \in PhilId: Request(p)
    \/ \E p \in PhilId: AcquireForks(p)
    \/ \E p \in PhilId: Eat(p)
    \/ \E p \in PhilId: FinishEat(p)

Spec == Init /\ [][Next]_<<forkOwner, forkState, philState>>

(* Helper predicates for progress *)
CanRequest(p) == philState[p] = "Thinking"
CanAcquire(p) == philState[p] = "Hungry" /\ forkOwner[LeftFork(p)]  = 0
                     /\ forkOwner[RightFork(p)] = 0
CanEat(p)     == philState[p] = "Hungry" /\ forkOwner[LeftFork(p)]  = p
                     /\ forkOwner[RightFork(p)] = p
CanFinish(p)  == philState[p] = "Eating"

NextEnabled == \E p \in PhilId : CanRequest(p) \/ CanAcquire(p) \/ CanEat(p) \/ CanFinish(p)

(* Invariants *)
NoTwoEating ==
    \A p,q \in PhilId :
        ~(Adjacent(p,q) /\ (philState[p] = "Eating" /\ philState[q] = "Eating"))

ForkOwnershipInvariant ==
    \A f \in ForkId :
        forkOwner[f] = 0 \/ 
        forkOwner[f] = LeftFork(f) \/ forkOwner[f] = RightFork(f)

(* Liveness *)
Liveness == []<> ( \E p \in PhilId : philState[p] = "Eating" )

(* Progress *)
Progress == [] NextEnabled

THEOREM Safety          == Spec => [] NoTwoEating
THEOREM Invariant1      == Spec => [] ForkOwnershipInvariant
THEOREM LivenessThm     == Fairness(Next) => Spec => Liveness
THEOREM ProgressThm     == Spec => Progress
=============================================================================