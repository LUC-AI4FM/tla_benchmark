--------------------------- MODULE QuicksortSpec ---------------------------
EXTENDS Naturals, TLC

CONSTANT N \* length of the array (positive integer)

VARIABLES a, S, pc

(* ------------------------------------------------------------------ *)
(* Helper definitions *)

Intervals == {x | x ∈ [low \in 1..N, high \in 1..N] /\ x.low <= x.high}

Count(v, f) == \#({i \in 1..N : f[i] = v})

IsPerm(f) == \A v \in 1..N : Count(v,f) = 1

PartitionConstraint(a', l, r, p) ==
   /\ (\A i \in l..p-1 : a'[i] <= a'[p])
   /\ (\A j \in p+1..r : a'[j] >= a'[p])

NewIntervals(l,r) == IF l > r THEN {} ELSE {[low |-> l, high |-> r]}

TypeOK ==
   /\ a ∈ [1..N -> 1..N]
   /\ S ⊆ Intervals
   /\ pc ∈ {"Start", "Done"}

(* ------------------------------------------------------------------ *)
(* Initial state *)

Init ==
   /\ TypeOK
   /\ a = [i \in 1..N |-> i]
   /\ S = {[low |-> 1, high |-> N]}
   /\ pc = "Start"

(* ------------------------------------------------------------------ *)
(* Actions *)

ProcessAction ==
   LET chooseInterval == CHOOSE ij ∈ S
        l == chooseInterval.low
        r == chooseInterval.high
   IN
      /\ pc' = "Start"
      /\ EXISTS p \in l..r :
           /\ EXISTS a' \in [1..N -> 1..N] :
                /\ (\A v \in 1..N : Count(v,a) = Count(v,a'))
                /\ PartitionConstraint(a', l, r, p)
      /\ S' = (S \ {chooseInterval}) ∪ NewIntervals(l,p-1) ∪ NewIntervals(p+1,r)

DoneAction ==
   /\ pc = "Start"
   /\ S = {}
   /\ a' = a
   /\ S' = S
   /\ pc' = "Done"

Next == ProcessAction \/ DoneAction

(* ------------------------------------------------------------------ *)
(* Specification *)

Spec == Init /\ [][Next]_<<a,S,pc>> /\ WF_Next(Next)

Safety ==
   TypeOK /\ IsPerm(a) /\ S ⊆ Intervals

Termination ==
   <> (pc = "Done")

THEOREM SafetyLemma : Spec => [] Safety
THEOREM TerminationLemma : Spec => Termination

============================================================================