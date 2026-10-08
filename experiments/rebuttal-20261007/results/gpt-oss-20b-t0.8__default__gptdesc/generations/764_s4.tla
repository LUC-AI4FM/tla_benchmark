MODULE DiningPhilosophers
EXTENDS Naturals

CONSTANTS N

VARIABLES sem, pc

(* Fork indices *)
RightFork(i) == (i + 1) MOD N
LeftFork(i)   == (i - 1 + N) MOD N

(* First and second forks for each philosopher *)
FirstFork(i)  == IF i = 0 THEN LeftFork(i) ELSE RightFork(i)
SecondFork(i) == IF i = 0 THEN RightFork(i) ELSE LeftFork(i)

(* Program counter states *)
THINKING == 0
FIRST    == 1
EATING   == 2

vars == <<sem, pc>>

Init ==
   /\ sem \in [0..N-1 -> 0]
   /\ pc  \in [0..N-1 -> THINKING]
   /\ \A i \in 0..N-1 : pc[i] = THINKING

AcquireFirstOne(i) ==
   /\ pc[i] = THINKING
   /\ sem[FirstFork(i)]