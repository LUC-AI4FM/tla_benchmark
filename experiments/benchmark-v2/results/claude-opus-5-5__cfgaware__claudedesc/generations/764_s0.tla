---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, TLC

CONSTANTS NP

ASSUME NP \in Nat /\ NP >= 2

(* --algorithm DiningPhilosophers

variables
    forks = [
        fork \in 1..NP |-> [
            holder |-> IF fork = 2 THEN 1 ELSE fork,
            clean |-> FALSE
        ]
    ]

define
LeftFork(p) == p
RightFork(p) == IF p = NP THEN 1 ELSE p + 1

LeftPhilosopher(p) == IF p = 1 THEN NP ELSE p - 1
RightPhilosopher(p) == IF p = NP THEN 1 ELSE p + 1

IsHoldingBothForks(p) ==
    forks[LeftFork(p)].holder = p /\ forks[RightFork(p)].holder = p
BothForksAreClean(p) ==
    forks[LeftFork(p)].clean /\ forks[RightFork(p)].clean

CanEat(p) == IsHoldingBothForks(p) /\ BothForksAreClean(p)
end define;

fair process Philosopher \in 1..NP
variables hungry = TRUE;
begin
Loop:
    while TRUE do
        if  /\ forks[LeftFork(self)].holder = self
            /\ ~forks[LeftFork(self)].clean
        then
            forks[LeftFork(self)] := [holder |-> LeftPhilosopher(self), clean |-> TRUE];
        elsif /\ forks[RightFork(self)].holder = self
              /\ ~forks[RightFork(self)].clean
        then
            forks[RightFork(self)] := [holder |-> RightPhilosopher(self), clean |-> TRUE];
        end if;
        if hungry then
            if CanEat(self) then
                Eat:
                    hungry := FALSE;
                    forks[LeftFork(self)].clean := FALSE ||
                    forks[RightFork(self)].clean := FALSE;
            end if;
        else
            Think:
                hungry := TRUE;
        end if;
    end while;
end process;

end algorithm *)

\* BEGIN TRANSLATION
VARIABLES forks, pc

(* define statement *)
LeftFork(p) == p
RightFork(p) == IF p = NP THEN 1 ELSE p + 1

LeftPhilosopher(p) == IF p = 1 THEN NP ELSE p - 1
RightPhilosopher(p) == IF p = NP THEN 1 ELSE p + 1

IsHoldingBothForksIn(f, p) ==
    f[LeftFork(p)].holder = p /\ f[RightFork(p)].holder = p
BothForksAreCleanIn(f, p) ==
    f[LeftFork(p)].clean /\ f[RightFork(p)].clean
CanEatIn(f, p) == IsHoldingBothForksIn(f, p) /\ BothForksAreCleanIn(f, p)

IsHoldingBothForks(p) == IsHoldingBothForksIn(forks, p)
BothForksAreClean(p) == BothForksAreCleanIn(forks, p)
CanEat(p) == CanEatIn(forks, p)

VARIABLE hungry

vars == << forks, pc, hungry >>

ProcSet == (1..NP)

Init == (* Global variables *)
        /\ forks = [ fork \in 1..NP |-> [
                        holder |-> IF fork = 2 THEN 1 ELSE fork,
                        clean |-> FALSE ] ]
        (* Process Philosopher *)
        /\ hungry = [self \in 1..NP |-> TRUE]
        /\ pc = [self \in ProcSet |-> "Loop"]

Loop(self) ==
    /\ pc[self] = "Loop"
    /\ LET nf ==
             IF /\ forks[LeftFork(self)].holder = self
                /\ ~forks[LeftFork(self)].clean
             THEN [forks EXCEPT ![LeftFork(self)] =
                       [holder |-> LeftPhilosopher(self), clean |-> TRUE]]
             ELSE IF /\ forks[RightFork(self)].holder = self
                     /\ ~forks[RightFork(self)].clean
                  THEN [forks EXCEPT ![RightFork(self)] =
                            [holder |-> RightPhilosopher(self), clean |-> TRUE]]
                  ELSE forks
       IN /\ forks' = nf
          /\ IF hungry[self]
                THEN IF CanEatIn(nf, self)
                        THEN pc' = [pc EXCEPT ![self] = "Eat"]
                        ELSE pc' = [pc EXCEPT ![self] = "Loop"]
                ELSE pc' = [pc EXCEPT ![self] = "Think"]
    /\ UNCHANGED hungry

Eat(self) ==
    /\ pc[self] = "Eat"
    /\ hungry' = [hungry EXCEPT ![self] = FALSE]
    /\ forks' = [forks EXCEPT ![LeftFork(self)].clean = FALSE,
                              ![RightFork(self)].clean = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "Loop"]

Think(self) ==
    /\ pc[self] = "Think"
    /\ hungry' = [hungry EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "Loop"]
    /\ UNCHANGED forks

Philosopher(self) == Loop(self) \/ Eat(self) \/ Think(self)

Next == (\E self \in 1..NP: Philosopher(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NP : WF_vars(Philosopher(self))

\* END TRANSLATION

TypeOK ==
    /\ forks \in [1..NP -> [holder : 1..NP, clean : BOOLEAN]]
    /\ hungry \in [1..NP -> BOOLEAN]
    /\ pc \in [ProcSet -> {"Loop", "Eat", "Think"}]

ExclusiveAccess ==
    \A p \in 1..NP :
        pc[p] = "Eat" =>
            /\ pc[LeftPhilosopher(p)] # "Eat"
            /\ pc[RightPhilosopher(p)] # "Eat"

NobodyStarves ==
    \A p \in 1..NP : []<>(pc[p] = "Eat")

=============================================================================