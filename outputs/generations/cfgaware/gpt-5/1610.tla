------------------------------ MODULE QuicksortPlusCal ------------------------------

EXTENDS Naturals

CONSTANT N

(*
PlusCal model (informal):

fair algorithm Quicksort
variables A, S;
begin
  with A0 \in [1..N -> 1..N] do
    A := A0;
  end with;
  S := IF N >= 1 THEN {[l |-> 1, r |-> N]} ELSE {};
qs1:
  while (S # {}) do
    with seg \in S do
      S := S \ {seg};
      with l = seg.l, r = seg.r do
        with p \in l..r do
          with Anew \in { A2 \in [1..N -> 1..N] :
                           Permuted(A, A2) /\ PartitionOK(A2, l, p, r) } do
            A := Anew;
            if l <= p-1 then S := S \cup {[l |-> l, r |-> p-1]} end if;
            if p+1 <= r then S := S \cup {[l |-> p+1, r |-> r]} end if;
          end with;
        end with;
      end with;
    end with;
  end while;
Done:
  skip;
end algorithm;
*)

Idx == 1..N

Intervals ==
  { [l |-> i, r |-> j] : i \in Idx, j \in Idx, i <= j }

IsInjective(f, S) ==
  /\ f \in [S -> S]
  /\ \A x \in S: \A y \in S: f[x] = f[y] => x = y

Perms(S) == { f \in [S -> S] : IsInjective(f, S) }

Permuted(A1, A2) ==
  \E pi \in Perms(Idx) :
    A2 = [ i \in Idx |-> A1[pi[i]] ]

PartitionOK(A2, l, p, r) ==
  /\ l \in Idx /\ r \in Idx
  /\ l <= p /\ p <= r
  /\ \A i \in (l .. (p - 1)) : A2[i] <= A2[p]
  /\ \A j \in ((p + 1) .. r) : A2[j] >= A2[p]

VARIABLES A, S, pc

vars == << A, S, pc >>

Init ==
  /\ pc = "qs1"
  /\ \E a \in [Idx -> Idx] : A = a
  /\ S = (IF N >= 1 THEN {[l |-> 1, r |-> N]} ELSE {})

qs1 ==
  /\ pc = "qs1"
  /\ IF S # {} THEN
       \E seg \in S :
         LET l == seg.l
             r == seg.r
         IN /\ l \in Idx /\ r \in Idx /\ l <= r
            /\ \E p \in l..r :
                 \E Anew \in [Idx -> Idx] :
                   /\ Permuted(A, Anew)
                   /\ PartitionOK(Anew, l, p, r)
                   /\ A' = Anew
                   /\ S' =
                        (S \ {seg})
                        \cup (IF l <= p - 1 THEN {[l |-> l, r |-> p - 1]} ELSE {})
                        \cup (IF p + 1 <= r THEN {[l |-> p + 1, r |-> r]} ELSE {})
            /\ pc' = "qs1"
     ELSE
       /\ UNCHANGED << A, S >>
       /\ pc' = "Done"

Next == qs1

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

==============================