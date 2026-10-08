----------------------------- MODULE DiningPhilosophers -----------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \land N \geq 1

P == 0..(N-1)

Succ(i) == IF i + 1 = N THEN 0 ELSE i + 1
Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

RFork(i) == i
LFork(i) == Pred(i)

VARIABLES state, forkOwner

vars == << state, forkOwner >>

Init ==
  /\ state = [i \in P |-> "Thinking"]
  /\ forkOwner = [f \in P |-> "Free"]

BeginHungry(i) ==
  /\ i \in P
  /\ state[i] = "Thinking"
  /\ state' = [state EXCEPT ![i] = "Hungry"]
  /\ UNCHANGED forkOwner

Acquire(i) ==
  /\ i \in P
  /\ state[i] = "Hungry"
  /\ forkOwner[LFork(i)] = "Free"
  /\ forkOwner[RFork(i)] = "Free"
  /\ state' = [state EXCEPT ![i] = "Eating"]
  /\ forkOwner' =
       [forkOwner EXCEPT
         ![LFork(i)] = i,
         ![RFork(i)] = i]

Release(i) ==
  /\ i \in P
  /\ state[i] = "Eating"
  /\ state' = [state EXCEPT ![i] = "Thinking"]
  /\ forkOwner' =
       [forkOwner EXCEPT
         ![LFork(i)] = "Free",
         ![RFork(i)] = "Free"]

Step(i) == BeginHungry(i) \/ Acquire(i) \/ Release(i)

Next == \E i \in P : Step(i)

Fairness ==
  /\ \A i \in P : SF_vars(BeginHungry(i))
  /\ \A i \in P : SF_vars(Acquire(i))
  /\ \A i \in P : WF_vars(Release(i))

Spec == Init /\ [][Next]_vars /\ Fairness

TypeOK ==
  /\ state \in [P -> {"Thinking", "Hungry", "Eating"}]
  /\ forkOwner \in [P -> (P \cup {"Free"})]

AdjacentNotBothEating ==
  \A i \in P :
    ~(state[i] = "Eating" /\ state[Succ(i)] = "Eating")

ResourceIntegrity ==
  /\ \A f \in P :
       forkOwner[f] = "Free" \/ forkOwner[f] \in P
  /\ \A f \in P :
       forkOwner[f] \in P => state[forkOwner[f]] = "Eating"
  /\ \A i \in P :
       state[i] = "Eating" =>
         /\ forkOwner[LFork(i)] = i
         /\ forkOwner[RFork(i)] = i
  /\ \A i \in P :
       state[i] # "Eating" =>
         /\ forkOwner[LFork(i)] # i
         /\ forkOwner[RFork(i)] # i

Inv == TypeOK /\ AdjacentNotBothEating /\ ResourceIntegrity
Safety == []Inv

EnabledStepExists == \E i \in P : ENABLED Step(i)
NoDeadlock == []<>(EnabledStepExists)

AttemptsInfOften ==
  \A i \in P : []<>(state[i] = "Hungry")

StarvationFreedom ==
  \A i \in P : []<>(state[i] = "Eating")

=============================================================================