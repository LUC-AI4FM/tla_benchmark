------------------------------- MODULE DiningPhilosophers -------------------------------
CONSTANTS NP

VARIABLES forks, philStates

(*--algorithm DiningPhilosophers
variables 
  forks = [i \in 1..NP -> <<IF i # 2 THEN (i-1) % NP ELSE 1, "dirty">>]],
          philStates = [p \in 1..NP -> FALSE];

process Philosopher \in 1..NP
begin
Loop:
    while TRUE do
        if forks[self][2] = "dirty" then
            forks[forks[self][1]][2] := "clean";
            forks[forks[self][1]] := <<(forks[self][1]+1) % NP, forks[forks[self][1]][2]>>;
        elsif philStates[self] /\ 
              (forks[self][1] = (self-1) % NP) /\ 
              (forks[(self+1) % NP][1] = self) /\
              (forks[self][2] = "clean") /\ 
              (forks[(self+1) % NP][2] = "clean")
        then
            philStates[self] := FALSE;
            forks[self][2] := "dirty";
            forks[(self+1) % NP][2] := "dirty";
            goto Eat;
        elsif ~philStates[self]
        then
            philStates[self] := TRUE;
            goto Think;
        end if;

Eat:
    skip;

Think:
    skip;
end process

end algorithm*)

Spec ==
  /\ Init
  /\ [][Next]_<<forks, philStates>>
  /\ WF_<<forks, philStates>>[Procs]
  /\ \A p \in 1..NP : WF_<<forks, philStates>>[Proc(p)]

Init ==
  /\ forks = [i \in 1..NP -> <<IF i # 2 THEN (i-1) % NP ELSE 1, "dirty">>]]
  /\ philStates = [p \in 1..NP -> FALSE]

Next ==
  \/ \E p \in 1..NP : Proc(p)

Proc(p) ==
  \/ LoopAction(p)
  \/ EatAction(p)
  \/ ThinkAction(p)

LoopAction(p) ==
  \/ (forks[p][2] = "dirty" /\ CleanAndPassFork(p))
  \/ (philStates[p] /\ CanEat(p) /\ EatTransition(p))
  \/ (~philStates[p] /\ ThinkTransition(p))

CleanAndPassFork(p) ==
  forks' = [forks EXCEPT ![p][2] = "clean", ![forks[p][1]] = <<(forks[p][1]+1) % NP, forks[forks[p][1]][2]>>]
  /\ philStates' = philStates

EatTransition(p) ==
  forks' = [forks EXCEPT ![p][2] = "dirty", ![(p+1) % NP][2] = "dirty"]
  /\ philStates' = [philStates EXCEPT ![p] = FALSE]

ThinkTransition(p) ==
  forks' = forks
  /\ philStates' = [philStates EXCEPT ![p] = TRUE]

CanEat(p) ==
  (forks[p][1] = (p-1) % NP) /\ 
  (forks[(p+1) % NP][1] = p) /\
  (forks[p][2] = "clean") /\ 
  (forks[(p+1) % NP][2] = "clean")

EatAction(p) ==
  forks' = forks
  /\ philStates' = philStates

ThinkAction(p) ==
  forks' = forks
  /\ philStates' = philStates

Procs == {Proc(p) : p \in 1..NP}

TypeOK ==
  /\ \A i \in 1..NP : forks[i] \in (0..NP-1) \X {"clean", "dirty"}
  /\ \A p \in 1..NP : philStates[p] \in BOOLEAN

ExclusiveAccess ==
  \A p, q \in 1..NP : 
    (p # q) => ~((philStates[p]) /\ (philStates[q]) /\
                (forks[p][1] = (q-1) % NP) /\ (forks[q][1] = p))

NobodyStarves ==
  \A p \in 1..NP : <>[] philStates[p]

=============================================================================