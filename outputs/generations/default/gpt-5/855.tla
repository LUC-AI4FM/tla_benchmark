------------------------- MODULE PrisonersAndSwitches -------------------------

EXTENDS Naturals

CONSTANTS N, Counter

ASSUME N \in Nat /\ N >= 2 /\ Counter \in 1..N

Prisoners == 1..N
NonCounters == Prisoners \ {Counter}
MaxTokens == 2 * (N - 1)

VARIABLES A, B, count, movedA, Visited

vars == << A, B, count, movedA, Visited >>

TypeOK ==
  /\ A \in BOOLEAN
  /\ B \in BOOLEAN
  /\ count \in Nat
  /\ movedA \in [Prisoners -> 0..2]
  /\ movedA[Counter] = 0
  /\ Visited \in [Prisoners -> BOOLEAN]

Init ==
  /\ A = FALSE
  /\ B = FALSE
  /\ count = 0
  /\ movedA = [i \in Prisoners |-> 0]
  /\ Visited = [i \in Prisoners |-> FALSE]

Step(p) ==
  /\ p \in Prisoners
  /\ Visited' = [Visited EXCEPT ![p] = TRUE]
  /\ IF p = Counter THEN
        IF A THEN
          /\ A' = FALSE
          /\ count' = count + 1
          /\ B' = B
          /\ movedA' = movedA
        ELSE
          /\ B' = ~B
          /\ UNCHANGED << A, count, movedA >>
     ELSE
        IF (~A) /\ (movedA[p] < 2) THEN
          /\ A' = TRUE
          /\ movedA' = [movedA EXCEPT ![p] = @ + 1]
          /\ B' = B
          /\ UNCHANGED count
        ELSE
          /\ B' = ~B
          /\ UNCHANGED << A, movedA, count >>

Next ==
  \E p \in Prisoners: Step(p)

Done == count = MaxTokens
AllVisited == \A i \in Prisoners: Visited[i]

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Prisoners: WF_vars(Step(p))

Safety ==
  [] (Done => AllVisited)

Liveness ==
  <> Done

=============================================================================