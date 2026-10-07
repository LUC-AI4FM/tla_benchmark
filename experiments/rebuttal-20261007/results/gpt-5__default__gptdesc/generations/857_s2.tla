------------------------------ MODULE PrisonerLightSwitch ------------------------------

EXTENDS Naturals, Integers

CONSTANTS N, Counter, KnownLightOff

ASSUME
  /\ N \in Nat
  /\ N >= 1
  /\ Counter \in 1..N
  /\ KnownLightOff \in BOOLEAN

Prisoners == 1..N
NonCounters == Prisoners \ {Counter}

Threshold == IF KnownLightOff THEN N ELSE 2*N - 1

VARIABLES
  light,          \* shared lamp: BOOLEAN
  tokens,         \* per-prisoner remaining "signal" tokens (non-counters: 1 if known-off, 2 if unknown; counter: 0)
  count,          \* counter's tally of "turning the light off" events
  victory,        \* TRUE once the counter announces victory
  visited,        \* set of prisoners who have visited the cell at least once
  cInitOnUsed     \* whether the counter has used his one permitted "turn light ON" action

vars == << light, tokens, count, victory, visited, cInitOnUsed >>

Init ==
  /\ IF KnownLightOff THEN light = FALSE ELSE light \in BOOLEAN
  /\ tokens = [p \in Prisoners |-> IF p = Counter THEN 0 ELSE IF KnownLightOff THEN 1 ELSE 2]
  /\ count = 0
  /\ victory = FALSE
  /\ visited = {}
  /\ cInitOnUsed = FALSE

Step(p) ==
  /\ ~victory
  /\ p \in Prisoners
  /\ visited' = visited \cup {p}
  /\ IF p = Counter THEN
        /\ tokens' = tokens
        /\ IF light = TRUE THEN
              /\ light' = FALSE
              /\ count' = count + 1
              /\ cInitOnUsed' = cInitOnUsed
           ELSE
              /\ IF ~cInitOnUsed /\ light = FALSE THEN
                    /\ light' = TRUE
                    /\ cInitOnUsed' = TRUE
                    /\ count' = count
                 ELSE
                    /\ UNCHANGED << light, cInitOnUsed, count >>
        /\ victory' = victory \/ (count' >= Threshold)
     ELSE
        /\ count' = count
        /\ cInitOnUsed' = cInitOnUsed
        /\ IF (light = FALSE) /\ (tokens[p] > 0) THEN
              /\ light' = TRUE
              /\ tokens' = [tokens EXCEPT ![p] = tokens[p] - 1]
           ELSE
              /\ UNCHANGED << light, tokens >>
        /\ victory' = victory

Next ==
  \/ \E p \in Prisoners : Step(p)
  \/ /\ victory
     /\ UNCHANGED vars

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Prisoners : WF_vars(Step(p))

AllVisited == visited = Prisoners

Safety == [](victory => AllVisited)

Liveness == <>victory

=============================================================================