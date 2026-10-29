------------------------------ MODULE PrisonersLightBulb ------------------------------
(***************************************************************************)
(* The "prisoners and a light bulb" puzzle with one shared lamp and a      *)
(* central announcement mechanism.                                         *)
(*                                                                         *)
(* N prisoners are isolated once the protocol starts. Repeatedly, and      *)
(* nondeterministically, one prisoner is placed alone in a room that has   *)
(* a lamp (on/off). Each visit may change the lamp. A prisoner may make a  *)
(* single final announcement that every prisoner has visited the room.    *)
(* If the announcement is correct the prisoners win; otherwise they lose.  *)
(*                                                                         *)
(* The prisoners agree on this strategy beforehand:                        *)
(*  - One distinguished prisoner (Counter) is the only one who switches    *)
(*    the lamp OFF. Each time the Counter finds the lamp ON, it switches   *)
(*    the lamp off and increments its private count.                       *)
(*  - Every other prisoner switches the lamp ON (when it finds it OFF) at  *)
(*    most MaxSignals times. Otherwise the prisoner never touches it.      *)
(*  - Only the Counter announces, and only when count reaches Threshold.   *)
(*                                                                         *)
(* Variants:                                                               *)
(*  - InitialLampKnown = TRUE : the lamp starts OFF, MaxSignals = 1, and   *)
(*                              Threshold = N - 1.                         *)
(*  - InitialLampKnown = FALSE: the lamp starts in an unknown state,       *)
(*                              MaxSignals = 2, and Threshold = 2(N - 1).  *)
(*    In this variant a spurious initial ON adds at most 1 to the count.   *)
(*    If one prisoner never visited, the count is at most                 *)
(*    2(N-2) + 1 < 2(N-1).                                                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,                 \* number of prisoners
    InitialLampKnown   \* TRUE: lamp initially off; FALSE: initial lamp state unknown

ASSUME NAssumption       == N \in Nat \ {0}
ASSUME LampKnownAssumption == InitialLampKnown \in BOOLEAN

Prisoners == 1..N
Counter   == 1                       \* the distinguished counting prisoner
Others    == Prisoners \ {Counter}

\* Per-prisoner signalling budget for non-counter prisoners
MaxSignals == IF InitialLampKnown THEN 1 ELSE 2

\* Victory threshold depends on whether the initial lamp state is known
Threshold  == IF InitialLampKnown THEN N - 1 ELSE 2 * (N - 1)

VARIABLES
    lamp,      \* current lamp state: TRUE = on, FALSE = off
    initLamp,  \* initial lamp state (ghost; used only for reasoning/invariants)
    count,     \* the Counter's private tally of legitimately observed signals
    signals,   \* signals[p]: number of times prisoner p has switched the lamp on
    visited,   \* ghost: set of prisoners who have actually visited the room
    status     \* "playing", "won" (correct announcement), "lost" (false announcement)

vars == <<lamp, initLamp, count, signals, visited, status>>

---------------------------------------------------------------------------------------
RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN  f[x] + SumOver(f, S \ {x})

\* Number of "tokens" the initial lamp state contributes
InitialBonus == IF initLamp THEN 1 ELSE 0

---------------------------------------------------------------------------------------
Init ==
    /\ lamp \in (IF InitialLampKnown THEN {FALSE} ELSE BOOLEAN)
    /\ initLamp = lamp
    /\ count = 0
    /\ signals = [p \in Prisoners |-> 0]
    /\ visited = {}
    /\ status = "playing"

(***************************************************************************)
(* The Counter's behaviour during a visit. The Counter increments only     *)
(* when it legitimately observes the lamp ON, and never beyond Threshold.  *)
(* When the count reaches Threshold, the Counter makes the single final    *)
(* announcement. The outcome is decided by the true visited set.          *)
(***************************************************************************)
CounterVisit(p) ==
    LET inc      == lamp /\ count < Threshold
        newCount == IF inc THEN count + 1 ELSE count
        nowSeen  == visited \cup {p}
    IN  /\ count'   = newCount
        /\ lamp'    = IF inc THEN FALSE ELSE lamp
        /\ signals' = signals
        /\ status'  = IF newCount >= Threshold
                         THEN IF nowSeen = Prisoners THEN "won" ELSE "lost"
                         ELSE "playing"

(***************************************************************************)
(* A non-counter prisoner's behaviour. The prisoner switches the lamp ON   *)
(* only if it is OFF and the prisoner still has signalling budget left.    *)
(* Otherwise the prisoner leaves the lamp alone. Non-counters never        *)
(* switch the lamp off and never announce.                                 *)
(***************************************************************************)
OtherVisit(p) ==
    /\ IF ~lamp /\ signals[p] < MaxSignals
          THEN /\ lamp'    = TRUE
               /\ signals' = [signals EXCEPT ![p] = @ + 1]
          ELSE UNCHANGED <<lamp, signals>>
    /\ UNCHANGED <<count, status>>

\* Prisoner p is chosen and placed alone in the room
Visit(p) ==
    /\ status = "playing"
    /\ visited' = visited \cup {p}
    /\ UNCHANGED initLamp
    /\ IF p = Counter THEN CounterVisit(p) ELSE OtherVisit(p)

\* After the game has ended, nothing changes (avoids spurious deadlock)
GameOver ==
    /\ status # "playing"
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Prisoners : Visit(p)
    \/ GameOver

\* Fairness: every prisoner is chosen infinitely often while the game is on
Fairness == \A p \in Prisoners : WF_vars(Visit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------------------
(***************************** Type & boundedness *************************)
TypeOK ==
    /\ lamp \in BOOLEAN
    /\ initLamp \in BOOLEAN
    /\ count \in 0..Threshold
    /\ signals \in [Prisoners -> 0..MaxSignals]
    /\ visited \subseteq Prisoners
    /\ status \in {"playing", "won", "lost"}

\* Non-counter prisoners never exceed their signalling budget
SignalBudget == \A p \in Others : signals[p] <= MaxSignals

\* The Counter never signals
CounterNeverSignals == signals[Counter] = 0

\* The count never exceeds the threshold
CountBounded == count <= Threshold

\* With a known initial state, the lamp starts off
KnownStartsOff == InitialLampKnown => ~initLamp

\* A prisoner with signal budget used has actually visited the room
SignalsImplyVisited == \A p \in Others : signals[p] > 0 => p \in visited

(*************************************************************************)
(* Token conservation. Each count increment corresponds to a lamp-ON     *)
(* token that is either a genuine signal or the initial lamp state.      *)
(* Hence the Counter increments only when it legitimately observes a     *)
(* signal.                                                               *)
(*************************************************************************)
TokenConservation ==
    SumOver(signals, Others) + InitialBonus = count + (IF lamp THEN 1 ELSE 0)

(******************************** Safety ***********************************)
Announced == status \in {"won", "lost"}

\* No false victory: an announcement is made only if everyone has visited
NoFalseVictory ==
    /\ status # "lost"
    /\ Announced => visited = Prisoners

\* The outcome is final once it has been announced
AnnouncementFinal ==
    [][ (status # "playing") => (status' = status) ]_vars

(******************************** Liveness *********************************)
\* Under fairness, the protocol eventually ends with a correct announcement
EventualVictory == <>(status = "won")

\* Every prisoner eventually visits the room
EveryoneEventuallyVisits == \A p \in Prisoners : <>(p \in visited)

=======================================================================================