MODULE Quicksort
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, DOMAIN

VARIABLES arr, initArr, subranges, pivots

(* Helper definitions *)
Count(x,s) ==
  Len({ i \in 1..Len(s) : s[i] = x })

IsPerm(a,b) == ∀x∈DOMAIN : Count(x,a) = Count(x,b)

SubrangeSet == { <<l,r>> | l \in 1..N /\ r \in 1..N /\ l <= r }

SumLengths(S) ==
  Sum({ (r - l + 1) : <<l,r>> \in S })

(* Subsequence and replacement helpers *)
SubSeq(a,l,r) == a[l .. r]

SubSeqReplace(a,l,r,b) ==
  LET prefix == IF l = 1 THEN [] ELSE a[1 .. l-1]
      suffix == IF r = N THEN [] ELSE a[r+1 .. N]
  IN prefix ++ b ++ suffix

Init ==
  /\ initArr \in { s \in Seq(DOMAIN) : Len(s) = N }
  /\ arr = initArr
  /\ subranges = { <<1,N>> }
  /\ pivots = [i \in 1..N |-> [j \in 1..N |-> ⊥]]

Partition ==
  ∃ l r p q s' :
    /\ <<l,r>> \in subranges
    /\ l <= p <= r
    /\ let oldSub == SubSeq(arr, l, r) in
       /\ s' \in { t | t \in Seq(DOMAIN) /\ Len(t)=r-l+1 }
       /\ ∀x∈DOMAIN : Count(x,s') = Count(x,oldSub)
       /\ l <= q <= r
       /\ s'[q - l + 1] = arr[p]
       /\ ∀ i j :
            i \in 1..(q-l) /\ j \in ((q-l+2)..Len(s')) => s'[i] <= s'[j]
       /\ arr' = SubSeqReplace(arr, l, r, s')
       /\ subranges' =
              (subranges \ {<<l,r>>})
              ∪ IF q > l THEN {<<l,q-1>>} ELSE {}
              ∪ IF q < r THEN {<<q+1,r>>} ELSE {}
       /\ pivots' = [i \in 1..N |-> [j \in 1..N |-> IF i=l /\ j=r THEN q ELSE pivots[i][j]]]

Next ==
  Partition

Spec ==
  Init /\ [][Next]_<<arr, initArr, subranges, pivots>>

(* Invariants *)
PermutationInvariant == IsPerm(arr, initArr)

OrderingInvariant ==
  ∀ <<l,r>> \in SubrangeSet :
    /\ <<l,r>> \notin subranges
    /\ pivots[l][r] # ⊥
    => ∃ q : pivots[l][r] = q
       /\ ∀ i j :
            i \in 1..(q-l) /\ j \in ((q-l+2)..(r-l+1)) =>
              arr[l + i - 1] <= arr[l + j - 1]

Safety == PermutationInvariant /\ OrderingInvariant

SpecWithInvariants == Spec /\ Safety

(* Liveness *)
Termination ==
  [] (subranges # {} => <> (subranges = {}))

Liveness == Termination

============================================================================)