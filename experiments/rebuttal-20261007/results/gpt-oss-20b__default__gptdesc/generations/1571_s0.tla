MODULE DiningPhilosophers
EXTENDS TLC

CONSTANT N

VARIABLES forks, state

(* Fork indices *)
Right(i) == i
Left(i) == (i - 1 + N) % N

FirstFork(i) == IF i = 0 THEN Left(i) ELSE Right(i)
SecondFork(i) == IF i = 0 THEN Right(i) ELSE Left(i)

Init ==
    /\