----------------------------- MODULE QuicksortPcalSpec -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLES a, S, pc

Indices == 1..N
Val == 1..N

vars == << a, S, pc >>

IntervalRec == [lo: Indices, hi: Indices]

TypeInv ==
  /\ a \in [Indices -> Val]
  /\ pc \in {"qs1", "Done"}
  /\ S \subseteq { iv \in IntervalRec : iv.lo < iv.hi }

Count(arr, v) == Cardinality({ i \in Indices : arr[i] = v })

Perm(arr1, arr2) ==
  /\ DOMAIN arr1 = Indices
  /\ DOMAIN arr2 = Indices
  /\ \A v \in Val :
       Count(arr1, v) = Count(arr2, v)

PartitionOK(arr, l, p, r) ==
  /\ l <= p /\ p <= r
  /\ \A i \in l .. (p - 1) : arr[i] <= arr[p]
  /\ \A i \in (p + 1) .. r : arr[i] >= arr[p]

NewIntervals(iv, p) ==
  { x \in {
      [lo |-> iv.lo, hi |-> p - 1],
      [lo |-> p + 1, hi |-> iv.hi]
    } :
      /\ 1 <= x.lo /\ x.hi <= N
      /\ x.lo < x.hi }

Init ==
  /\ a \in [Indices -> Val]
  /\ S = IF N >= 2 THEN { [lo |-> 1, hi |-> N] } ELSE {}
  /\ pc = "qs1"

qs1 ==
  /\ pc = "qs1"
  /\ IF S = {} THEN
        /\ pc' = "Done"
        /\ UNCHANGED << a, S >>
     ELSE
        \E iv \in S :
        \E p \in iv.lo .. iv.hi :
        \E anew \in [Indices -> Val] :
          /\ Perm(anew, a)
          /\ PartitionOK(anew, iv.lo, p, iv.hi)
          /\ a' = anew
          /\ S' = (S \ {iv}) \cup NewIntervals(iv, p)
          /\ pc' = "qs1"

Next == qs1

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

Invariant == TypeInv

THEOREM Spec => []Invariant

THEOREM Spec => Termination
=============================================================================