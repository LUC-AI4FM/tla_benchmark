------------------------------- MODULE QuicksortPlusCal -------------------------------
EXTENDS Naturals

CONSTANT N

IndexSet == 1..N
Arrays == [IndexSet -> IndexSet]

AllIntervals ==
  { [l |-> l, r |-> r] : l \in IndexSet /\ r \in IndexSet /\ l <= r }

ProperIntervals ==
  { i \in AllIntervals : i.l < i.r }

IsInterval(i) ==
  i \in AllIntervals

Range(i) == i.l..i.r

Permutations ==
  { f \in [IndexSet -> IndexSet] :
      /\ \A x, y \in IndexSet: f[x] = f[y] => x = y
      /\ \A y \in IndexSet: \E x \in IndexSet: f[x] = y }

Permuted(b, a) ==
  \E f \in Permutations:
    b = [ i \in IndexSet |-> a[f[i]] ]

PartitionOK(b, p, i) ==
  /\ p \in Range(i)
  /\ \A j \in Range(i): j < p => b[j] <= b[p]
  /\ \A j \in Range(i): j > p => b[j] >= b[p]

NewIntervals(i, p) ==
  { j \in { [l |-> i.l, r |-> p-1], [l |-> p+1, r |-> i.r] } :
      /\ IsInterval(j)
      /\ j.l < j.r }

VARIABLES A, S, pc

vars == << A, S, pc >>

Init ==
  /\ A \in Arrays
  /\ S = IF N >= 2 THEN { [l |-> 1, r |-> N] } ELSE {}
  /\ pc = "qs1"

qs1 ==
  /\ pc = "qs1"
  /\ S /= {}
  /\ \E i \in S:
       \E p \in Range(i):
         \E b \in Arrays:
           /\ Permuted(b, A)
           /\ PartitionOK(b, p, i)
           /\ A' = b
           /\ S' = (S \ { i }) \cup NewIntervals(i, p)
           /\ pc' = "qs1"

doneAct ==
  /\ pc = "qs1"
  /\ S = {}
  /\ pc' = "Done"
  /\ UNCHANGED << A, S >>

Next == qs1 \/ doneAct

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeInv ==
  /\ A \in Arrays
  /\ S \subseteq ProperIntervals
  /\ pc \in { "qs1", "Done" }

Termination == <> (pc = "Done")
=============================================================================