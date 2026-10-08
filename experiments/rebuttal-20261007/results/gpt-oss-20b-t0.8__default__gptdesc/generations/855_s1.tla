----------------------------- MODULE PrisonersSwitches -----------------------------
EXTENDS Naturals, TLC

CONSTANTS N, Counter
ASSUME Counter \in 1..N

Proc == 1 .. N

VARIABLES SwitchA, SwitchB, Count, Visited, UpCount, Done

vars == <<SwitchA, SwitchB, Count, Visited, UpCount, Done>>

Init ==
   /\ SwitchA = FALSE
   /\ SwitchB = FALSE
   /\ Count = 0
   /\ Visited = {}
   /\ UpCount = [i \in Proc |-> 0]
   /\ Done = FALSE

PSelect(p) ==
   LET
     upAllowed == (p # Counter) /\ UpCount[p] < 2 /\ SwitchA = FALSE
   IN
   IF p = Counter THEN
      IF SwitchA = TRUE THEN
          /\ SwitchA' = FALSE
          /\ Count' = Count + 1
          /\ SwitchB' = SwitchB
          /\ Done' = IF (Count + 1) = N - 1 THEN TRUE ELSE Done
          /\ Visited' = Visited ∪ {Counter}
          /\ UpCount' = UpCount
      ELSE
          /\ SwitchA' = SwitchA
          /\ Count' = Count
          /\ SwitchB' = NOT SwitchB
          /\ Done' = Done
          /\ Visited' = Visited ∪ {Counter}
          /\ UpCount' = UpCount
   ELSE  \* non‑counter prisoner
      IF upAllowed THEN
         /\ SwitchA' = TRUE
         /\ UpCount' = [UpCount EXCEPT ![p] = UpCount[p] + 1]
         /\ Count' = Count
         /\ SwitchB' = SwitchB
         /\ Done' = Done
         /\ Visited' = Visited ∪ {p}
      ELSE
         /\ SwitchA' = SwitchA
         /\ UpCount' = UpCount
         /\ Count' = Count
         /\ SwitchB' = NOT SwitchB
         /\ Done' = Done
         /\ Visited' = Visited ∪ {p}

Next == \E p \in Proc : PSelect(p)

Spec ==
   Init /\ [][Next]_vars
   /\ WEAK FAIRNESS (\E p \in Proc : PSelect(p))

Inv == Done => Visited = Proc

THEOREM Safety == Spec => []Inv
THEOREM Liveness == Spec => <>Done
=====================================================================