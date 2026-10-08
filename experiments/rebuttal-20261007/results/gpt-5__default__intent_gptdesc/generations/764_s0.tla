------------------------- MODULE DiningPhilosophers -------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    N,                 \* Number of philosophers (N >= 2)
    ForkStates,        \* Abstract set of fork states
    EatOK,             \* Subset of ForkStates that permits eating
    EatTrans,          \* Allowed state-change relation on a fork when a philosopher starts eating
    GiveTrans          \* Allowed state-change relation on a fork when it is passed

ASSUME N \in { n \in Nat : n >= 2 }
ASSUME ForkStates # {}
ASSUME EatOK \subseteq ForkStates
ASSUME EatTrans \subseteq (ForkStates \X ForkStates)
ASSUME GiveTrans \subseteq (ForkStates \X ForkStates)

(*
  Indexing:
  - Philosophers are P == 0..(N-1).
  - Fork i is the fork between philosopher i and Right(i).
  - Owner[i] is either i or Right(i).
*)

P == 0..(N-1)

Right(i) == (i + 1) % N
Left(i)  == (i + N - 1) % N

Dir == {"L","R"}
Opp(d) == IF d = "L" THEN "R" ELSE "L"
Nbr(i, d) == IF d = "L" THEN Left(i) ELSE Right(i)
ForkOf(i, d) == IF d = "L" THEN Left(i) ELSE i

VARIABLES
    ph,       \* phase of each philosopher: "thinking", "hungry", or "eating"
    owner,    \* owner[f] is the philosopher who currently holds fork f
    fstate,   \* fstate[f] is the current abstract state of fork f
    req       \* req[i][d] indicates philosopher i currently requests fork in direction d

vars == << ph, owner, fstate, req >>

PhStates == {"thinking", "hungry", "eating"}

HasRight(i) == owner[i] = i
HasLeft(i)  == owner[Left(i)] = i
Has(i, d)   == IF d = "L" THEN HasLeft(i) ELSE HasRight(i)
HasBoth(i)  == HasLeft(i) /\ HasRight(i)

PermitsEat(i) == /\ fstate[Left(i)] \in EatOK
                 /\ fstate[i] \in EatOK

TypeOK ==
    /\ ph \in [P -> PhStates]
    /\ owner \in [P -> P]
    /\ \A f \in P: owner[f] \in {f, Right(f)}
    /\ fstate \in [P -> ForkStates]
    /\ req \in [P -> [Dir -> BOOLEAN]]

ForkOwnerOK == \A f \in P: owner[f] \in {f, Right(f)}

NoNeighborsEating == \A i \in P: ~(ph[i] = "eating" /\ ph[Right(i)] = "eating")

Init ==
    /\ ph = [i \in P |-> "thinking"]
    /\ owner \in [P -> P]
    /\ \A f \in P: owner[f] \in {f, Right(f)}
    /\ fstate \in [P -> ForkStates]
    /\ req = [i \in P |-> [d \in Dir |-> FALSE]]

ThinkToHungry(i) ==
    /\ i \in P
    /\ ph[i] = "thinking"
    /\ ph' = [ph EXCEPT ![i] = "hungry"]
    /\ req' = [req EXCEPT
                  ![i]["L"] = ~HasLeft(i),
                  ![i]["R"] = ~HasRight(i)]
    /\ UNCHANGED << owner, fstate >>

StartEating(i) ==
    /\ i \in P
    /\ ph[i] = "hungry"
    /\ HasBoth(i)
    /\ PermitsEat(i)
    /\ \E sL \in ForkStates, sR \in ForkStates:
         /\ << fstate[Left(i)], sL >> \in EatTrans
         /\ << fstate[i],       sR >> \in EatTrans
         /\ fstate' = [fstate EXCEPT ![Left(i)] = sL, ![i] = sR]
         /\ ph' = [ph EXCEPT ![i] = "eating"]
         /\ req' = [req EXCEPT ![i]["L"] = FALSE, ![i]["R"] = FALSE]
         /\ UNCHANGED owner

StopEating(i) ==
    /\ i \in P
    /\ ph[i] = "eating"
    /\ ph' = [ph EXCEPT ![i] = "thinking"]
    /\ UNCHANGED << owner, fstate, req >>

RequestFork(i, d) ==
    /\ i \in P
    /\ d \in Dir
    /\ ph[i] \in {"hungry", "eating"}
    /\ ~Has(i, d)
    /\ ~req[i][d]
    /\ req' = [req EXCEPT ![i][d] = TRUE]
    /\ UNCHANGED << ph, owner, fstate >>

GiveFork(i, d) ==
    /\ i \in P
    /\ d \in Dir
    /\ LET j == Nbr(i, d) IN
       LET f == ForkOf(i, d) IN
       LET od == Opp(d) IN
         /\ owner[f] = i
         /\ ph[i] # "eating"
         /\ owner' = [owner EXCEPT ![f] = j]
         /\ \E sNew \in ForkStates:
              /\ << fstate[f], sNew >> \in GiveTrans
              /\ fstate' = [fstate EXCEPT ![f] = sNew]
         /\ req' = [req EXCEPT ![j][od] = FALSE]
         /\ UNCHANGED ph

Proc(i) ==
    /\ i \in P
    /\ ( ThinkToHungry(i)
       \/ StartEating(i)
       \/ StopEating(i)
       \/ (\E d \in Dir: RequestFork(i, d))
       \/ (\E d \in Dir: GiveFork(i, d))
       )

Next ==
    \E i \in P:
       ThinkToHungry(i)
       \/ StartEating(i)
       \/ StopEating(i)
       \/ (\E d \in Dir: RequestFork(i, d))
       \/ (\E d \in Dir: GiveFork(i, d))

Fairness ==
    \A i \in P: WF_vars(Proc(i))

Spec == Init /\ [][Next]_vars /\ Fairness

(*
  Safety properties (temporal):
  - Mutual exclusion on shared forks (no neighboring philosophers eat simultaneously).
*)
Safety == []NoNeighborsEating

(*
  State invariants:
  - Forks are always held by exactly one adjacent philosopher.
  - All variables respect their intended types/ranges.
*)
StateInv == TypeOK /\ ForkOwnerOK

(*
  Liveness:
  - Under the per-philosopher weak-fairness assumptions (Fairness),
    every philosopher who becomes hungry will eventually eat (no starvation).
*)
NoStarvation == \A i \in P: [](ph[i] = "hungry" => <> (ph[i] = "eating"))

(*
  Progress (no global deadlock):
  - The system is always able to make a next step.
*)
NoDeadlock == []ENABLED Next

=============================================================================