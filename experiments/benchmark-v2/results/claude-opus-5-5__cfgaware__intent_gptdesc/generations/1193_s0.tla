---------------------------- MODULE PrimedExprs ----------------------------
EXTENDS Integers, FiniteSets

VARIABLES x, y

vars == <<x, y>>

MaxX == 5

Init == /\ x = 1
        /\ y = 1

(* Branch 1: only the first component changes; y is unchanged. *)
IncOnly ==
    /\ x < MaxX
    /\ x' = x + 1
    /\ y' = y

(* Branch 2: x increases and y is set to 1. The value of y' is
   constrained by the new value of x. *)
IncAndReset ==
    /\ x < MaxX
    /\ x' = x + 1
    /\ (x' = 2) => (y' = 1)
    /\ y' = 1

(* Branch 3: set- and function-valued expressions that refer to
   next-state values. *)
IncWithSets ==
    /\ x < MaxX
    /\ x' \in {x + 1}
    /\ {x'} \subseteq (x + 1)..(x + 1)
    /\ LET f == [i \in {1, 2} |-> i]
           g == [f EXCEPT ![1] = x']
       IN  /\ DOMAIN g = {1, 2}
           /\ g[1] = x'
           /\ g[2] = 2
    /\ y' \in {1}

(* Branch 4: guarded choice with an embedded assertion. Any choice
   that violates the assertion is disallowed. *)
GuardedChoice ==
    /\ x < MaxX
    /\ \E v \in {x + 1, x + 2}:
          /\ v = x + 1          \* assertion: only the +1 step is allowed
          /\ x' = v
    /\ \E w \in {0, 1}:
          /\ (x' = 2) => (w = 1) \* assertion: conditional consistency
          /\ w = 1
          /\ y' = w

(* Terminal stuttering once the bound is reached, to avoid deadlock. *)
Done ==
    /\ x >= MaxX
    /\ UNCHANGED vars

Next == \/ IncOnly
        \/ IncAndReset
        \/ IncWithSets
        \/ GuardedChoice
        \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK == /\ x \in Int
          /\ y \in Int

Inv == /\ TypeOK
        /\ x \in 1..MaxX
        /\ y = 1

(* Action property: whenever x' = 2 in a step that updates y, y' = 1. *)
CondConsistency == [][(x' = 2 /\ y' # y) => (y' = 1)]_vars

(* Liveness: at least two distinct states are reached. *)
Progress == <>(x >= 2)
=============================================================================