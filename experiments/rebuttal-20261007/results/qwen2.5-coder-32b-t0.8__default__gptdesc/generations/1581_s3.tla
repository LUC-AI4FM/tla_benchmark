------------------------------- MODULE DiningPhilosophers -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N

VARIABLES pc, sem

Init == 
  /\ pc = << FORALL i \in 0..N-1 : "think" >>
  /\ sem = [FORALL f \in 0..N-1 : TRUE]

RightFork(p) == p
LeftFork(p)  == (p - 1) % N

PickupRightFork(p) ==
  /\ sem[RightFork(p)]
  /\ sem' = [sem EXCEPT ![RightFork(p)] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "tryLeft"]

PickupLeftFork(p) ==
  /\ sem[LeftFork(p)]
  /\ sem' = [sem EXCEPT ![LeftFork(p)] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "eat"]

PutDownForks(p) ==
  /\ sem' = [sem EXCEPT ![RightFork(p)] = TRUE, ![LeftFork(p)] = TRUE]
  /\ pc' = [pc EXCEPT ![p] = "think"]

Think(p) ==
  /\ pc[p] = "think"
  /\ \/ UNCHANGED pc
     \/ pc' = [pc EXCEPT ![p] = IF p # 0 THEN "tryRight" ELSE "tryLeft"]
  /\ UNCHANGED sem

TryRightFork(p) ==
  /\ pc[p] = "tryRight"
  /\ PickupRightFork(p)

TryLeftFork(p) ==
  /\ pc[p] = "tryLeft"
  /\ PickupLeftFork(p)

Eat(p) ==
  /\ pc[p] = "eat"
  /\ \/ UNCHANGED pc
     \/ PutDownForks(p)
  /\ UNCHANGED sem

Next ==
  \/ \E p \in 0..N-1 : Think(p)
  \/ \E p \in 0..N-1 : TryRightFork(p)
  \/ \E p \in 0..N-1 : TryLeftFork(p)
  \/ \E p \in 0..N-1 : Eat(p)

Spec ==
  /\ Init
  /\ [][Next]_<<pc, sem>>
  /\ WF_pc(Next)

MutualExclusion == 
  \A p1 \in 0..N-1, p2 \in 0..N-1 :
    \/ p1 = p2
    \/ ~(pc[p1] = "eat" /\ pc[p2] = "eat")

StarvationFreedom ==
  \A p \in 0..N-1 : 
    [](<>[] (pc[p] = "eat"))

====