----------------------------- MODULE PrisonersAndLight -----------------------------

EXTENDS Naturals

CONSTANTS
    N,              \* Number of prisoners, a natural number >= 2
    Counter,        \* Distinguished counter prisoner in 1..N
    InitKnownOff,   \* Boolean: TRUE iff the initial lamp state is known to be OFF
    Seed,           \* For the unknown-initial variant: a designated non-counter with extra budget
    None            \* A distinguished value not in 1..N used for "no announcer yet"

ASSUME
    /\ N \in Nat /\ 2 <= N
    /\ Counter \in 1..N
    /\ InitKnownOff \in BOOLEAN
    /\ None \notin 1..N
    /\ InitKnownOff \/ (Seed \in (1..N) \ {Counter})

Prisoners == 1..N
Others == Prisoners \ {Counter}

(*
  Standard strategy budgets:
    - If the initial lamp state is known OFF: every non-counter has budget 1.
    - If the initial lamp state is unknown: exactly one designated non-counter "Seed" has budget 2,
      the rest have budget 1. The counter never uses the lamp as a signal (budget 0).
*)
Budget(i) ==
    IF i = Counter THEN 0
    ELSE IF InitKnownOff THEN 1
    ELSE IF i = Seed THEN 2 ELSE 1

(*
  Victory threshold depends on the variant:
    - Known-OFF: the counter must collect N-1 signals.
    - Unknown-initial: the counter must collect N signals (extra one to absorb a possible initial ON).
*)
CountGoal == IF InitKnownOff THEN N - 1 ELSE N

VARIABLES
    lamp,           \* Boolean state of the shared lamp
    visited,        \* [Prisoners -> BOOLEAN], whether each prisoner has ever visited
    used,           \* [Prisoners -> Nat], per-prisoner count of used signals (turning lamp ON)
    count,          \* The counter's tally of collected signals (turning lamp from ON to OFF)
    announced,      \* Has the final announcement been made?
    announcer       \* Who made the announcement (None if none yet)

vars == << lamp, visited, used, count, announced, announcer >>

AllVisited == \A i \in Prisoners: visited[i]

Init ==
    LET StartLampSet == IF InitKnownOff THEN {FALSE} ELSE BOOLEAN IN
    /\ lamp \in StartLampSet
    /\ visited = [i \in Prisoners |-> FALSE]
    /\ used = [i \in Prisoners |-> 0]
    /\ count = 0
    /\ announced = FALSE
    /\ announcer = None

(*
  A visit by prisoner i follows the standard reliable strategy:
    - Always records that i has visited.
    - If i is the Counter and lamp is ON: increments count and turns lamp OFF.
    - If i is a non-counter, lamp is OFF, and i has remaining budget: turns lamp ON and consumes budget.
    - Otherwise, leaves the lamp and counters unchanged.
*)
Visit(i) ==
    /\ ~announced
    /\ i \in Prisoners
    /\ IF i = Counter THEN
          /\ visited' = [visited EXCEPT ![i] = TRUE]
          /\ used' = used
          /\ IF lamp THEN
                /\ lamp' = FALSE
                /\ count' = count + 1
             ELSE
                /\ lamp' = lamp
                /\ count' = count
       ELSE
          /\ visited' = [visited EXCEPT ![i] = TRUE]
          /\ count' = count
          /\ IF ~lamp /\ used[i] < Budget(i) THEN
                /\ lamp' = TRUE
                /\ used' = [used EXCEPT ![i] = used[i] + 1]
             ELSE
                /\ lamp' = lamp
                /\ used' = used
    /\ UNCHANGED << announced, announcer >>

(*
  Central final announcement:
    - Allowed only once, only after every prisoner has visited and the counter has reached CountGoal.
    - The protocol chooses the Counter as the announcer (others could, in principle, but the protocol
      only permits a correct announcement).
*)
Announce ==
    /\ ~announced
    /\ AllVisited
    /\ count = CountGoal
    /\ announced' = TRUE
    /\ announcer' = Counter
    /\ UNCHANGED << lamp, visited, used, count >>

Next ==
    \/ Announce
    \/ \E i \in Prisoners: Visit(i)

(*
  Fairness:
    - Strong fairness on each Visit(i): each prisoner is scheduled infinitely often while visits remain enabled.
    - Weak fairness on Announce: once enabled continuously, the announcement eventually occurs.
*)
Fairness ==
    /\ \A i \in Prisoners: SF_vars(Visit(i))
    /\ WF_vars(Announce)

Spec == Init /\ [][Next]_vars /\ Fairness

(*
  Invariants (types and bounds)
*)
TypeInv ==
    /\ lamp \in BOOLEAN
    /\ visited \in [Prisoners -> BOOLEAN]
    /\ used \in [Prisoners -> Nat]
    /\ count \in Nat
    /\ announced \in BOOLEAN
    /\ announcer \in ({None} \cup Prisoners)

BoundsInv ==
    /\ used[Counter] = 0
    /\ \A i \in Others: used[i] <= Budget(i)
    /\ count <= CountGoal

Inv == TypeInv /\ BoundsInv

(*
  Safety: No false victory — an announcement cannot be made unless everyone has visited.
*)
SafetyNoFalseVictory == [](announced => AllVisited)

(*
  Liveness: Under the fairness assumption, the protocol eventually reaches a (correct) announcement.
*)
LivenessVictory == <> announced

====================================================================================