------------------------------- MODULE Consensus -------------------------------
(***************************************************************************)
(* Abstract specification of the consensus problem.                        *)
(*                                                                         *)
(* A set of processes may propose values from the parameter set Values.    *)
(* At most once, a single proposed value becomes chosen. Processes may     *)
(* then learn the chosen value. Communication details are abstracted away. *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Values,      \* the set of values that may be proposed and chosen
          Processes    \* the set of processes (proposers and learners)

ASSUME ValuesAssumption    == Values # {} /\ IsFiniteSet(Values)
ASSUME ProcessesAssumption == Processes # {} /\ IsFiniteSet(Processes)

(* A value distinct from every allowed value, meaning "nothing learned yet". *)
NoValue == CHOOSE v : v \notin Values

VARIABLES proposed,  \* set of values proposed so far
          chosen,    \* set of chosen values (empty or a singleton)
          learned    \* learned[p] = value learned by p, or NoValue

vars == << proposed, chosen, learned >>

-----------------------------------------------------------------------------
(* Type correctness *)

TypeOK ==
    /\ proposed \subseteq Values
    /\ chosen \subseteq Values
    /\ learned \in [Processes -> Values \cup {NoValue}]

-----------------------------------------------------------------------------
(* Initial condition: nothing proposed, nothing chosen, nothing learned. *)

Init ==
    /\ proposed = {}
    /\ chosen = {}
    /\ learned = [p \in Processes |-> NoValue]

-----------------------------------------------------------------------------
(* Actions *)

(* Process p proposes value v. *)
Propose(p, v) ==
    /\ v \notin proposed
    /\ proposed' = proposed \cup {v}
    /\ UNCHANGED << chosen, learned >>

(* A single transition that selects one proposed value. It is enabled  *)
(* only while nothing is chosen, so it can occur at most once.          *)
Choose ==
    /\ chosen = {}
    /\ \E v \in proposed : chosen' = {v}
    /\ UNCHANGED << proposed, learned >>

(* Process p learns the chosen value. *)
Learn(p) ==
    /\ learned[p] = NoValue
    /\ \E v \in chosen : learned' = [learned EXCEPT ![p] = v]
    /\ UNCHANGED << proposed, chosen >>

ProposeStep == \E p \in Processes, v \in Values : Propose(p, v)

Next ==
    \/ ProposeStep
    \/ Choose
    \/ \E p \in Processes : Learn(p)

-----------------------------------------------------------------------------
(* Specifications *)

(* Safety-only specification. *)
Spec == Init /\ [][Next]_vars

(* Weak fairness: continuously enabled Choose and Learn actions are not   *)
(* postponed forever. Proposing is not forced, so if nothing is ever      *)
(* proposed, choosing nothing is a permitted outcome (nontriviality).     *)
Fairness ==
    /\ WF_vars(Choose)
    /\ \A p \in Processes : WF_vars(Learn(p))

FairSpec == Spec /\ Fairness

(* Variant additionally requiring that proposals are eventually made. *)
FairSpecWithProposals == FairSpec /\ WF_vars(ProposeStep)

-----------------------------------------------------------------------------
(* Safety properties (invariants) *)

(* (1) Validity: any chosen value comes from the allowed set and was proposed. *)
Validity ==
    /\ chosen \subseteq Values
    /\ chosen \subseteq proposed

(* (2) Agreement: at most one distinct value is chosen. *)
Agreement ==
    /\ Cardinality(chosen) <= 1
    /\ \A v, w \in chosen : v = w

(* Learned values are consistent with the chosen value. *)
LearnedConsistency ==
    \A p \in Processes :
        learned[p] # NoValue => learned[p] \in chosen

(* Any two processes that learned agree. *)
LearnerAgreement ==
    \A p, q \in Processes :
        (learned[p] # NoValue /\ learned[q] # NoValue) => learned[p] = learned[q]

Safety == TypeOK /\ Validity /\ Agreement /\ LearnedConsistency /\ LearnerAgreement

(* (3) Integrity: once a value is chosen it remains chosen and is never   *)
(* replaced by a different value (an action property).                   *)
Integrity ==
    [][chosen # {} => chosen' = chosen]_vars

LearnedStable ==
    [][\A p \in Processes : learned[p] # NoValue => learned'[p] = learned[p]]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

(* (4)/(5) Eventual choice, conditioned on at least one proposal: if some  *)
(* value is proposed, some allowed value is eventually chosen. If nothing *)
(* is ever proposed, choosing nothing is permitted. Check under FairSpec. *)
EventualChoice ==
    (proposed # {}) ~> (chosen # {} /\ chosen \subseteq Values)

(* Every process eventually learns once a value is chosen (under FairSpec). *)
EventualLearning ==
    (chosen # {}) ~> (\A p \in Processes : learned[p] # NoValue)

(* Unconditional eventual choice; holds under FairSpecWithProposals. *)
EventuallyChosen ==
    <>(\E v \in Values : chosen = {v})

-----------------------------------------------------------------------------
(* Theorems *)

THEOREM Spec => []Safety
THEOREM Spec => Integrity /\ LearnedStable
THEOREM FairSpec => EventualChoice /\ EventualLearning
THEOREM FairSpecWithProposals => EventuallyChosen
=============================================================================