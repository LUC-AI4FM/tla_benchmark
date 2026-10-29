------------------------------- MODULE AbstractOpSystem -------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    InitState,   \* the initial integer value of the state
    Op,          \* operation family: a function from states to sets of successor states
    InvSet,      \* user-specified invariant set: the state must always stay in it
    GoalSet      \* states whose eventual reachability is to be checked

VARIABLE x

vars == <<x>>

ASSUME InitAssump == InitState \in Int
ASSUME OpAssump   == /\ DOMAIN Op \subseteq Int
                     /\ \A s \in DOMAIN Op : Op[s] \subseteq Int
ASSUME InvAssump  == InvSet \subseteq Int
ASSUME GoalAssump == GoalSet \subseteq Int

(* Op may be partial: states outside DOMAIN Op have no successors. *)
Successors(s) == IF s \in DOMAIN Op THEN Op[s] ELSE {}

--------------------------------------------------------------------------------------
Init == x = InitState

(* Every transition picks a next state from Op(current). *)
Step(s) == /\ s \in Successors(x)
           /\ x' = s

Next == \E s \in Successors(x) : Step(s)

(* Weak fairness: if a transition is continuously possible, one is eventually taken. *)
Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------------
(* Safety properties *)

TypeOK == x \in Int

(* The state always stays within the parameterized invariant set. *)
StateInv == x \in InvSet

(* Every step taken is consistent with Op. *)
StepsRespectOp == [][x' \in Successors(x)]_vars

(* Deadlock freedom: every reachable state has a nonempty set of successors. *)
NoDeadlock == Successors(x) # {}

(* The system can perform a transition whenever Op(current) is nonempty. *)
EnabledWhenNonempty == (Successors(x) # {}) => ENABLED Next

--------------------------------------------------------------------------------------
(* Liveness properties *)

(* Whenever a state-changing transition is possible, one is eventually taken
   or it stops being possible. *)
Progress == []<>(<<Next>>_vars \/ ~ENABLED <<Next>>_vars)

(* Whenever Op(current) is nonempty and some successor changes the state,
   the state eventually changes. *)
EventuallyMoves ==
    \A v \in Int :
        ((x = v /\ \E s \in Successors(v) : s # v) ~> (x # v))

(* Reachability: on every behavior, a goal state is eventually reached. *)
EventuallyReachesGoal == <>(x \in GoalSet)

(* Possible reachability (existential): check NotGoal as an invariant;
   a counterexample is a witness trace reaching a goal state. *)
NotGoal == x \notin GoalSet

--------------------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => StepsRespectOp
=======================================================================================