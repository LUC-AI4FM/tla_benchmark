---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT NP

ASSUME NP \in Nat /\ NP > 1

Philosophers == 1..NP
Forks == 1..NP

LeftFork(p) == p
RightFork(p) == IF p = NP THEN 1 ELSE p + 1

LeftPhilosopher(f) == f
RightPhilosopher(f) == IF f = 1 THEN NP ELSE f - 1

(* --algorithm DiningPhilosophers
variables
    forks = [f \in Forks |-> 
        IF f = 2 
        THEN [holder |-> 1, clean |-> FALSE]
        ELSE [holder |-> IF LeftPhilosopher(f) < RightPhilosopher(f) 
                         THEN LeftPhilosopher(f) 
                         ELSE RightPhilosopher(f), 
              clean |-> FALSE]];

fair process philosopher \in Philosophers
variables hungry = TRUE;
begin
Loop:
    while TRUE do
        \* Pass dirty forks to requesting neighbors
        if forks[LeftFork(self)].holder = self /\ forks[LeftFork(self)].clean = FALSE /\ self # LeftPhilosopher(LeftFork(self)) then
            forks[LeftFork(self)] := [holder |-> LeftPhilosopher(LeftFork(self)), clean |-> TRUE];
        elsif forks[LeftFork(self)].holder = self /\ forks[LeftFork(self)].clean = FALSE /\ self = LeftPhilosopher(LeftFork(self)) /\ RightPhilosopher(LeftFork(self)) # self then
            forks[LeftFork(self)] := [holder |-> RightPhilosopher(LeftFork(self)), clean |-> TRUE];
        elsif forks[RightFork(self)].holder = self /\ forks[RightFork(self)].clean = FALSE /\ self # LeftPhilosopher(RightFork(self)) then
            forks[RightFork(self)] := [holder |-> LeftPhilosopher(RightFork(self)), clean |-> TRUE];
        elsif forks[RightFork(self)].holder = self /\ forks[RightFork(self)].clean = FALSE /\ self = LeftPhilosopher(RightFork(self)) /\ RightPhilosopher(RightFork(self)) # self then
            forks[RightFork(self)] := [holder |-> RightPhilosopher(RightFork(self)), clean |-> TRUE];
        elsif hungry /\ forks[LeftFork(self)].holder = self /\ forks[RightFork(self)].holder = self then
            goto Eat;
        elsif ~hungry then
            goto Think;
        end if;
    end while;

Eat:
    hungry := FALSE;
    forks[LeftFork(self)] := [holder |-> self, clean |-> FALSE];
    forks[RightFork(self)] := [holder |-> self, clean |-> FALSE];
    goto Loop;

Think:
    hungry := TRUE;
    goto Loop;
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES forks, pc, hungry

vars == << forks, pc, hungry >>

ProcSet == (Philosophers)

Init == (* Global variables *)
        /\ forks = [f \in Forks |->
                       IF f = 2
                       THEN [holder |-> 1, clean |-> FALSE]
                       ELSE [holder |-> IF LeftPhilosopher(f) < RightPhilosopher(f)
                                        THEN LeftPhilosopher(f)
                                        ELSE RightPhilosopher(f),
                             clean |-> FALSE]]
        (* Process philosopher *)
        /\ hungry = [self \in Philosophers |-> TRUE]
        /\ pc = [self \in ProcSet |-> "Loop"]

Loop(self) == /\ pc[self] = "Loop"
              /\ IF forks[LeftFork(self)].holder = self /\ forks[LeftFork(self)].clean = FALSE /\ self # LeftPhilosopher(LeftFork(self))
                    THEN /\ forks' = [forks EXCEPT ![LeftFork(self)] = [holder |-> LeftPhilosopher(LeftFork(self)), clean |-> TRUE]]
                         /\ pc' = [pc EXCEPT ![self] = "Loop"]
                    ELSE IF forks[LeftFork(self)].holder = self /\ forks[LeftFork(self)].clean = FALSE /\ self = LeftPhilosopher(LeftFork(self)) /\ RightPhilosopher(LeftFork(self)) # self
                            THEN /\ forks' = [forks EXCEPT ![LeftFork(self)] = [holder |-> RightPhilosopher(LeftFork(self)), clean |-> TRUE]]
                                 /\ pc' = [pc EXCEPT ![self] = "Loop"]
                            ELSE IF forks[RightFork(self)].holder = self /\ forks[RightFork(self)].clean = FALSE /\ self # LeftPhilosopher(RightFork(self))
                                    THEN /\ forks' = [forks EXCEPT ![RightFork(self)] = [holder |-> LeftPhilosopher(RightFork(self)), clean |-> TRUE]]
                                         /\ pc' = [pc EXCEPT ![self] = "Loop"]
                                    ELSE IF forks[RightFork(self)].holder = self /\ forks[RightFork(self)].clean = FALSE /\ self = LeftPhilosopher(RightFork(self)) /\ RightPhilosopher(RightFork(self)) # self
                                            THEN /\ forks' = [forks EXCEPT ![RightFork(self)] = [holder |-> RightPhilosopher(RightFork(self)), clean |-> TRUE]]
                                                 /\ pc' = [pc EXCEPT ![self] = "Loop"]
                                            ELSE IF hungry[self] /\ forks[LeftFork(self)].holder = self /\ forks[RightFork(self)].holder = self
                                                    THEN /\ pc' = [pc EXCEPT ![self] = "Eat"]
                                                         /\ forks' = forks
                                                    ELSE IF ~hungry[self]
                                                            THEN /\ pc' = [pc EXCEPT ![self] = "Think"]
                                                                 /\ forks' = forks
                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "Loop"]
                                                                 /\ forks' = forks
              /\ hungry' = hungry

Eat(self) == /\ pc[self] = "Eat"
             /\ hungry' = [hungry EXCEPT ![self] = FALSE]
             /\ forks' = [forks EXCEPT ![LeftFork(self)] = [holder |-> self, clean |-> FALSE],
                                       ![RightFork(self)] = [holder |-> self, clean |-> FALSE]]
             /\ pc' = [pc EXCEPT ![self] = "Loop"]

Think(self) == /\ pc[self] = "Think"
               /\ hungry' = [hungry EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "Loop"]
               /\ forks' = forks

philosopher(self) == Loop(self) \/ Eat(self) \/ Think(self)

Next == (\E self \in Philosophers: philosopher(self))

Spec == Init /\ [][Next]_vars /\ \A self \in Philosophers: WF_vars(philosopher(self))

\* END TRANSLATION

TypeOK == /\ forks \in [Forks -> [holder: Philosophers, clean: BOOLEAN]]
          /\ hungry \in [Philosophers -> BOOLEAN]
          /\ pc \in [Philosophers -> {"Loop", "Eat", "Think"}]

IsEating(p) == pc[p] = "Eat"

ExclusiveAccess == \A p \in Philosophers: 
    ~(IsEating(p) /\ IsEating(IF p = NP THEN 1 ELSE p + 1))

NobodyStarves == \A p \in Philosophers: []<>(pc[p] = "Eat")

=============================================================================