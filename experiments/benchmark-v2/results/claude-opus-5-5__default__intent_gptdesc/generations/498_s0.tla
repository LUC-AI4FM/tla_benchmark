------------------------- MODULE MultiConsensus -------------------------
(***************************************************************************)
(* An abstract multi-instance consensus service. Proposers add values     *)
(* from a fixed nonempty domain Values. Each slot in the fixed nonempty    *)
(* set Slots independently and nondeterministically chooses at most one   *)
(* previously proposed value. Choices are final. No algorithm or message  *)
(* pattern is prescribed.                                                  *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANTS Values,   \* the value domain
          Slots     \* the set of independent consensus instances

ASSUME ValuesNonempty == Values # {}
ASSUME SlotsNonempty  == Slots # {}

VARIABLES proposed,  \* set of values proposed so far (system-wide)
          chosen     \* chosen[s] : set of values chosen for slot s

vars == <<proposed, chosen>>

---------------------------------------------------------------------------
(* Type invariant: chosen values per slot are finite subsets of Values.  *)
TypeOK ==
    /\ proposed \subseteq Values
    /\ chosen \in [Slots -> SUBSET Values]
    /\ \A s \in Slots : IsFiniteSet(chosen[s])

---------------------------------------------------------------------------
Init ==
    /\ proposed = {}
    /\ chosen = [s \in Slots |-> {}]

(* A proposer introduces a new value at any time.                         *)
Propose(v) ==
    /\ v \in Values
    /\ v \notin proposed
    /\ proposed' = proposed \cup {v}
    /\ UNCHANGED chosen

(* Slot s, not yet decided, decides some previously proposed value.       *)
Choose(s) ==
    /\ chosen[s] = {}
    /\ \E v \in proposed :
          chosen' = [chosen EXCEPT ![s] = {v}]
    /\ UNCHANGED proposed

ProposeAny == \E v \in Values : Propose(v)

Next ==
    \/ ProposeAny
    \/ \E s \in Slots : Choose(s)

Fairness ==
    /\ WF_vars(ProposeAny)
    /\ \A s \in Slots : WF_vars(Choose(s))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety properties                                                      *)

\* Every chosen value for any slot was proposed.
ChosenWasProposed ==
    \A s \in Slots : chosen[s] \subseteq proposed

\* No slot ever has more than one chosen value.
AtMostOneChosen ==
    \A s \in Slots : Cardinality(chosen[s]) <= 1

SafetyInv == TypeOK /\ ChosenWasProposed /\ AtMostOneChosen

\* Chosen values are persistent: once decided, a slot never changes.
ChosenPersistent ==
    [][\A s \in Slots : chosen[s] # {} => chosen'[s] = chosen[s]]_vars

\* Proposals are never withdrawn (supports "proposed at some point").
ProposedMonotone ==
    [][proposed \subseteq proposed']_vars

---------------------------------------------------------------------------
(* Liveness: every slot eventually acquires a chosen value.               *)
EventuallyDecided ==
    \A s \in Slots : <>(chosen[s] # {})

---------------------------------------------------------------------------
THEOREM Spec => []SafetyInv
THEOREM Spec => ChosenPersistent
THEOREM Spec => ProposedMonotone
THEOREM Spec => EventuallyDecided
==========================================================================