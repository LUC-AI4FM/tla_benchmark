----------------------------- MODULE CMDiningPhilosophers -----------------------------

EXTENDS Integers, TLC

CONSTANT NP

ASSUME NP \in Nat /\ NP >= 2

(*
--algorithm CMChandyMisra
variables forks;

fair process (Philo \in ProcSet)
variables hungry = TRUE;
begin
Loop:
  if forks[LeftFork(self)].holder = self /\ ~forks[LeftFork(self)].clean then
    forks[LeftFork(self)].clean := TRUE;
    forks[LeftFork(self)].holder := LeftOf(self);
  elsif forks[RightFork(self)].holder = self /\ ~forks[RightFork(self)].clean then
    forks[RightFork(self)].clean := TRUE;
    forks[RightFork(self)].holder := RightOf(self);
  elsif hungry /\ forks[LeftFork(self)].holder = self /\ forks[RightFork(self)].holder = self
        /\ forks[LeftFork(self)].clean /\ forks[RightFork(self)].clean then
    goto Eat;
  elsif ~hungry then
    goto Think;
  end if;
  goto Loop;

Eat:
  hungry := FALSE;
  forks[LeftFork(self)].clean := FALSE;
  forks[RightFork(self)].clean := FALSE;
  goto Loop;

Think:
  hungry := TRUE;
  goto Loop;
end process;
end algorithm;
*)

VARIABLES forks, pc, hungry

ProcSet == 0 .. (NP - 1)
ForkSet == ProcSet

LeftOf(i)  == (i + 1) % NP
RightOf(i) == (i - 1) % NP

(*
 We index forks so that fork k is between philosophers k and (k - 1) % NP.
 For philosopher i:
   - Right fork is k = i   (between i and (i - 1) % NP)
   - Left  fork is k = i+1 (between (i + 1) % NP and i)
*)
RightFork(i) == i
LeftFork(i)  == (i + 1) % NP

Lbls == {"Loop", "Eat", "Think"}

Holder0(k) ==
  IF k = 2 THEN 1
  ELSE IF k = 0 THEN 0 ELSE k - 1

Init ==
  /\ forks \in [ForkSet -> [holder: ProcSet, clean: BOOLEAN]]
  /\ forks = [k \in ForkSet |-> [holder |-> Holder0(k), clean |-> FALSE]]
  /\ pc \in [ProcSet -> Lbls]
  /\ pc = [i \in ProcSet |-> "Loop"]
  /\ hungry \in [ProcSet -> BOOLEAN]
  /\ hungry = [i \in ProcSet |-> TRUE]

HasLeft(i)  == forks[LeftFork(i)].holder = i
HasRight(i) == forks[RightFork(i)].holder = i
CleanLeft(i)  == forks[LeftFork(i)].clean
CleanRight(i) == forks[RightFork(i)].clean
NoDirtyHeld(i) == ~(HasLeft(i) /\ ~CleanLeft(i)) /\ ~(HasRight(i) /\ ~CleanRight(i))
CanEat(i) == hungry[i] /\ HasLeft(i) /\ HasRight(i) /\ CleanLeft(i) /\ CleanRight(i)

LoopPassLeft(i) ==
  /\ pc[i] = "Loop"
  /\ HasLeft(i) /\ ~CleanLeft(i)
  /\ forks' = [forks EXCEPT
                 ![LeftFork(i)].holder = LeftOf(i),
                 ![LeftFork(i)].clean  = TRUE]
  /\ UNCHANGED << pc, hungry >>

LoopPassRight(i) ==
  /\ pc[i] = "Loop"
  /\ HasRight(i) /\ ~CleanRight(i)
  /\ forks' = [forks EXCEPT
                 ![RightFork(i)].holder = RightOf(i),
                 ![RightFork(i)].clean  = TRUE]
  /\ UNCHANGED << pc, hungry >>

LoopGotoEat(i) ==
  /\ pc[i] = "Loop"
  /\ NoDirtyHeld(i)
  /\ CanEat(i)
  /\ pc' = [pc EXCEPT ![i] = "Eat"]
  /\ UNCHANGED << forks, hungry >>

LoopGotoThink(i) ==
  /\ pc[i] = "Loop"
  /\ NoDirtyHeld(i)
  /\ ~hungry[i]
  /\ pc' = [pc EXCEPT ![i] = "Think"]
  /\ UNCHANGED << forks, hungry >>

EatStep(i) ==
  /\ pc[i] = "Eat"
  /\ hungry' = [hungry EXCEPT ![i] = FALSE]
  /\ forks' = [forks EXCEPT
                 ![LeftFork(i)].clean  = FALSE,
                 ![RightFork(i)].clean = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "Loop"]

ThinkStep(i) ==
  /\ pc[i] = "Think"
  /\ hungry' = [hungry EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "Loop"]
  /\ UNCHANGED forks

ProcStep(i) ==
    LoopPassLeft(i)
  \/ LoopPassRight(i)
  \/ LoopGotoEat(i)
  \/ LoopGotoThink(i)
  \/ EatStep(i)
  \/ ThinkStep(i)

Next ==
  \E i \in ProcSet: ProcStep(i)

vars == << forks, pc, hungry >>

Spec ==
  Init /\ [][Next]_vars /\ (\A i \in ProcSet: WF_vars(ProcStep(i)))

TypeOK ==
  /\ forks \in [ForkSet -> [holder: ProcSet, clean: BOOLEAN]]
  /\ \A k \in ForkSet: forks[k].holder \in {k, (k - 1) % NP}
  /\ pc \in [ProcSet -> Lbls]
  /\ hungry \in [ProcSet -> BOOLEAN]

EatingNow(i) == pc[i] = "Eat"

ExclusiveAccess ==
  \A i \in ProcSet:
    /\ ~(EatingNow(i) /\ EatingNow(LeftOf(i)))
    /\ ~(EatingNow(i) /\ EatingNow(RightOf(i)))

NobodyStarves ==
  \A i \in ProcSet: []<>(pc[i] = "Eat")

================================================================================