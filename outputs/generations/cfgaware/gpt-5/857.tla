------------------------------ MODULE PrisonerSwitch ------------------------------

EXTENDS Naturals, TLC

CONSTANTS N, Counter, UnknownInit

(***************************************************************************)
(* Basic sets and parameters *)
(***************************************************************************)
P == 1..N
NonCounters == P \ {Counter}
MaxSignals == IF UnknownInit THEN 2 ELSE 1
Goal == IF UnknownInit THEN 2*N - 1 ELSE N - 1

(***************************************************************************)
(* State variables *)
(***************************************************************************)
VARIABLES
  light,      \* shared lamp: TRUE = on, FALSE = off
  visited,    \* [P -> BOOLEAN], whether each prisoner has ever visited
  used,       \* [P -> 0..MaxSignals], number of signals used by each non-counter
  count,      \* counter's tally of observed signals (turn-offs)
  announced,  \* whether victory has been announced
  seed        \* for unknown-initial variant: whether counter has performed one seeding "turn-on"
  
Vars == << light, visited, used, count, announced, seed >>

(***************************************************************************)
(* Typing invariant *)
(***************************************************************************)
TypeOK ==
  /\ light \in BOOLEAN
  /\ visited \in [P -> BOOLEAN]
  /\ used \in [P -> 0..MaxSignals]
  /\ count \in Nat
  /\ announced \in BOOLEAN
  /\ seed \in BOOLEAN
  /\ Counter \in P

(***************************************************************************)
(* Initial states *)
(***************************************************************************)
Init ==
  /\ (IF UnknownInit THEN light \in BOOLEAN ELSE light = FALSE)
  /\ visited = [p \in P |-> FALSE]
  /\ used    = [p \in P |-> 0]
  /\ count = 0
  /\ announced = FALSE
  /\ seed = FALSE

(***************************************************************************)
(* Per-prisoner step *)
(***************************************************************************)
CanSignal(p) ==
  /\ p \in NonCounters
  /\ ~announced
  /\ ~light
  /\ used[p] < MaxSignals

ActNonCounter(p) ==
  /\ p \in P
  /\ p # Counter
  /\ visited' = [visited EXCEPT ![p] = TRUE]
  /\ used'    = [used EXCEPT ![p] = IF CanSignal(p) THEN used[p] + 1 ELSE used[p]]
  /\ light'   = IF CanSignal(p) THEN TRUE ELSE light
  /\ count' = count
  /\ seed' = seed
  /\ announced' = announced

ActCounter(p) ==
  /\ p = Counter
  /\ visited' = [visited EXCEPT ![p] = TRUE]
  /\ LET nLight ==
         IF ~announced /\ light THEN FALSE
         ELSE IF ~announced /\ ~light /\ UnknownInit /\ ~seed THEN TRUE
         ELSE light
     nCount ==
         IF ~announced /\ light THEN count + 1 ELSE count
     nSeed ==
         IF ~announced /\ ~light /\ UnknownInit /\ ~seed THEN TRUE ELSE seed
     nAnnounced ==
         announced \/ (nCount >= Goal)
     IN  /\ light' = nLight
         /\ count' = nCount
         /\ seed'  = nSeed
         /\ announced' = nAnnounced
         /\ used' = used

Step(p) == ActCounter(p) \/ ActNonCounter(p)

(***************************************************************************)
(* Global next-state relation *)
(***************************************************************************)
Next ==
  IF ~announced
    THEN \E p \in P : Step(p)
    ELSE UNCHANGED Vars

(***************************************************************************)
(* Specification with weak fairness of the warden's selection *)
(***************************************************************************)
Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A p \in P : WF_Vars(Step(p))

(***************************************************************************)
(* Liveness: eventually, victory is announced *)
(***************************************************************************)
Terminating == <>announced

(***************************************************************************)
(* Safety: any victory announcement implies everyone has visited *)
(***************************************************************************)
VictoryOK == announced => \A p \in P : visited[p]

=============================================================================