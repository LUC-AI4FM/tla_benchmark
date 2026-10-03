---- MODULE QuickSortSpec ----
EXTENDS Naturals, Integers, Sequences

(*
This module specifies a recursive quicksort over an array of length ArrayLen.
A commented PlusCal sketch (not executable) for intuition:

--algorithm QS
variables A \in [1..ArrayLen -> Int], A0 = A, stack;

procedure QS(l, r) {
  if l < r then
    with p \in l..r, Anew \in [1..ArrayLen -> Int] do
      assume Partition(A, Anew, l, r, p);
      A := Anew;
      call QS(l, p);
      call QS(p+1, r);
    end with;
  end if;
}

begin
  A \in [1..ArrayLen -> Int];
  A0 := A;
  if ArrayLen = 0 then
    stack := << >>;
  else
    stack := << [l |-> 1, r |-> ArrayLen] >>;
  end if;
  while stack # << >> do
    with f = Head(stack) do
      if f.l >= f.r then
        stack := Tail(stack);
      else
        with p \in f.l..f.r, Anew \in [1..ArrayLen -> Int] do
          assume Partition(A, Anew, f.l, f.r, p);
          A := Anew;
          stack := Tail(stack) \o << [l |-> p+1, r |-> f.r], [l |-> f.l, r |-> p] >>;
        end with;
      end if;
    end with;
  end while;
end algorithm;

The TLA+ below is a hand-written translation capturing the same behavior.
*)

CONSTANT ArrayLen

Indices == 1..ArrayLen

Bijections(S) ==
  { f \in [S -> S] :
      /\ \A x, y \in S: f[x] = f[y] => x = y
      /\ \A y \in S: \E x \in S: f[x] = y
  }

IsPermutation(a, b) ==
  \E p \in Bijections(Indices): b = [i \in Indices |-> a[p[i]]]

Sorted(a) ==
  \A i, j \in Indices: i < j => a[i] <= a[j]

Partition(a, a2, l, r, p) ==
  /\ a2 \in [Indices -> Int]
  /\ IsPermutation(a, a2)
  /\ \A i \in Indices \ (l..r): a2[i] = a[i]
  /\ l <= p /\ p <= r
  /\ \A i \in l..p: \A j \in (p+1)..r: a2[i] <= a2[j]

VARIABLES A, A0, stack, pc

vars == << A, stack, pc, A0 >>

TypeOK ==
  /\ A \in [Indices -> Int]
  /\ A0 \in [Indices -> Int]
  /\ stack \in Seq([l: Nat, r: Nat])
  /\ pc \in {"Work", "Done"}

Init ==
  /\ ArrayLen \in Nat
  /\ A0 \in [Indices -> Int]
  /\ A = A0
  /\ IF ArrayLen = 0
        THEN stack = << >>
        ELSE stack = << [l |-> 1, r |-> ArrayLen] >>
  /\ pc = IF stack = << >> THEN "Done" ELSE "Work"

Next ==
  /\ pc = "Work"
  /\ stack /= << >>
  /\ LET f == Head(stack) IN
     \/ /\ f.l >= f.r
        /\ A' = A
        /\ A0' = A0
        /\ stack' = Tail(stack)
        /\ pc' = IF Tail(stack) = << >> THEN "Done" ELSE "Work"
     \/ /\ f.l < f.r
        /\ \E p \in f.l..f.r:
             \E Anew \in [Indices -> Int]:
               /\ Partition(A, Anew, f.l, f.r, p)
               /\ A' = Anew
               /\ A0' = A0
               /\ stack' =
                    LET left  == [l |-> f.l, r |-> p]
                        right == [l |-> p+1, r |-> f.r]
                    IN Tail(stack) \o << right, left >>
               /\ pc' = "Work"

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

FinalCheck == (pc = "Done") => /\ IsPermutation(A0, A) /\ Sorted(A)

====