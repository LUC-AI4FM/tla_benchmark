MODULE DiningPhilosophers
EXTENDS Naturals, Sequences, TLC

CONSTANT N \in Nat

VARIABLES sem, pc

Forks == 0 .. N-1
Philo == Forks

vars == <<sem, pc>>

Init ==
    /\ sem = [j \in Forks |-> 1]
    /\ pc = [i \in Philo |-> "Idle"]

AcquireRight(i) ==
    /\ i \in Philo
    /\ i # 0
    /\ pc[i] = "Idle"
    /\ sem[i] = 1
    /\ sem' = [sem EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = "AcquireRight"]

AcquireLeft(i) ==
    /\ i \in Philo
    /\ i # 0
    /\ pc[i] = "AcquireRight"
    /\ sem[(i-1) % N] = 1
    /\ sem' = [sem EXCEPT ![(i-1) % N] = 0]
    /\ pc' = [pc EXCEPT ![i] = "AcquireLeft"]

Eat(i) ==
    /\ i \in Philo
    /\ i # 0
    /\ pc[i] = "AcquireLeft"
    /\ pc' = [pc EXCEPT ![i] = "Eating"]
    /\ sem' = sem

ReleaseRight(i) ==
    /\ i \in Philo
    /\ i # 0
    /\ pc[i] = "Eating"
    /\ sem' = [sem EXCEPT ![i] = 1]
    /\ pc' = [pc EXCEPT ![i] = "ReleaseRight"]

ReleaseLeft(i) ==
    /\ i \in Philo
    /\ i # 0
    /\ pc[i] = "ReleaseRight"
    /\ sem' = [sem EXCEPT ![(i-1) % N] = 1]
    /\ pc' = [pc EXCEPT ![i] = "Idle"]

AcquireLeft0 ==
    /\ pc[0] = "Idle"
    /\ sem[N-1] = 1
    /\ sem' = [sem EXCEPT ![N-1] = 0]
    /\ pc' = [pc EXCEPT ![0] = "AcquireLeft"]

AcquireRight0 ==
    /\ pc[0] = "AcquireLeft"
    /\ sem[0] = 1
    /\ sem' = [sem EXCEPT ![0] = 0]
    /\ pc' = [pc EXCEPT ![0] = "AcquireRight"]

Eat0 ==
    /\ pc[0] = "AcquireRight"
    /\ pc' = [pc EXCEPT ![0] = "Eating"]
    /\ sem' = sem

ReleaseLeft0 ==
    /\ pc[0] = "Eating"
    /\ sem' = [sem EXCEPT ![N-1] = 1]
    /\ pc' = [pc EXCEPT ![0] = "ReleaseLeft"]

ReleaseRight0 ==
    /\ pc[0] = "ReleaseLeft"
    /\ sem' = [sem EXCEPT ![0] = 1]
    /\ pc' = [pc EXCEPT ![0] = "Idle"]

Next ==
    \E i \in Philo : (i # 0) /\ (
        AcquireRight(i)
      \/ AcquireLeft(i)
      \/ Eat(i)
      \/ ReleaseRight(i)
      \/ ReleaseLeft(i))
    \/ AcquireLeft0
    \/ AcquireRight0
    \/ Eat0
    \/ ReleaseLeft0
    \/ ReleaseRight0

Invariant ==
    \A i \in Philo :
        ~(pc[i] = "Eating" /\ pc[(i+1) % N] = "Eating")

StarvationFree ==
    \A i \in Philo : []<>(pc[i] = "Eating")

Spec == Init /\ [][Next]_vars /\ SF_vars(Next)

============================================================================