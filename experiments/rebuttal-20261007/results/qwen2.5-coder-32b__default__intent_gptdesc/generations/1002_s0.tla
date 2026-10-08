------------------------------- MODULE BarrierSync -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N \* Number of processes
ASSUME N > 0

VARIABLES phase, round \* phase[p] is the phase of process p; round is the current round number

PHASES == {"arrive", "release"}

Init == /\ phase = [p \in 1..N -> "arrive"]
        /\ round = 0

Next ==
    \/ \/ \E p \in 1..N : phase[p] = "arrive" /\ phase' = [phase EXCEPT ![p] = "release"] /\ round' = round
       /\ \A q \in 1..N \ {p} : phase'[q] = phase[q]
    \/ \/ \A p \in 1..N : phase[p] = "release"
       /\ phase' = [p \in 1..N -> "arrive"]
       /\ round' = round + 1

Spec ==
    /\ Init
    /\ [][Next]_<<phase, round>>
    /\ WF_next(<<phase, round>>)

\* Safety: No process may be released until all processes have arrived.
TypeOK == /\ phase \in [1..N -> PHASES]
          /\ round \in Nat

AllArrived ==
    \A p \in 1..N : phase[p] = "arrive"

Safety ==
    [](phase[p] = "release" => AllArrived)

\* Liveness: Whenever all processes eventually arrive, they will all eventually be released.
Liveness ==
    <>(AllArrived) ~> <>(\A p \in 1..N : phase[p] = "release")

\* Reusability: After a release, the barrier resets so processes can participate in subsequent rounds without confusion between rounds.
Reusability ==
    [](phase[p] = "arrive" /\ round = r => <>[phase[p] = "release"]_<<phase>>)

=============================================================================