------------------------------- MODULE Quicksort -------------------------------

EXTENDS Integers, Sequences

CONSTANTS ArrayLen, Val

ASSUME ArrayLen \in Nat
ASSUME Val \subseteq Int

(*
--algorithm QS
variables A \in [1..ArrayLen -> Val];

procedure QS(l, r)
{   if l < r then
        with p \in l..r-1 do
            A := some permutation A' of A that
                 - keeps A[k] unchanged for k \notin l..r, and
                 - partitions l..r at p, i.e.,
                   \A i \in l..p, j \in (p+1)..r : A'[i] <= A'[j];
            call QS(l, p);
            call QS(p+1, r);
        end with;
    end if;
}

begin
    if ArrayLen > 0 then call QS(1, ArrayLen); end if;
end algorithm;
*)

VARIABLES
    A,     \* current array (function 1..ArrayLen -> Val)
    A0,    \* initial array snapshot
    stack, \* sequence of frames, each a record [l |-> ..., r |-> ...]
    pc     \* control state: "Loop" or "Done"

Indices == 1..ArrayLen

Frames == [l : Indices, r : Indices]

ValidFrame(fr) == fr \in Frames /\ fr.l <= fr.r

FramesOK(s) ==
  /\ s \in Seq(Frames)
  /\ \A i \in 1..Len(s) : ValidFrame(s[i])

SetImage(f, S) == { f[x] : x \in S }

InjectiveOn(S, f) ==
  \A i \in S : \A j \in S : i # j => f[i] # f[j]

BijOn(S, f) ==
  /\ f \in [S -> S]
  /\ InjectiveOn(S, f)
  /\ SetImage(f, S) = S

Perm(A1, A2) ==
  \E p \in [Indices -> Indices] :
    /\ BijOn(Indices, p)
    /\ \A i \in Indices : A1[i] = A2[p[i]]

PermuteWithin(A1, A2, l, r) ==
  LET S == l..r IN
    /\ \A k \in (Indices \ S) : A2[k] = A1[k]
    /\ \E h \in [S -> S] :
         /\ BijOn(S, h)
         /\ \A i \in S : A2[i] = A1[h[i]]

PartitionedAt(A2, l, r, p) ==
  /\ l \leq p /\ p < r
  /\ \A i \in l..p : \A j \in (p+1)..r : A2[i] <= A2[j]

Sorted(A1) ==
  \A i \in Indices : \A j \in Indices : (i < j) => A1[i] <= A1[j]

TypeInv ==
  /\ A \in [Indices -> Val]
  /\ A0 \in [Indices -> Val]
  /\ pc \in {"Loop", "Done"}
  /\ FramesOK(stack)

PermInv == Perm(A, A0)

Postcondition == [](pc = "Done" => /\ Perm(A, A0) /\ Sorted(A))

Termination == <> (pc = "Done")

Init ==
  /\ A \in [Indices -> Val]
  /\ A0 = A
  /\ stack =
       IF ArrayLen = 0
       THEN << >>
       ELSE << [l |-> 1, r |-> ArrayLen] >>
  /\ pc = "Loop"

Next ==
  \/
  /\ pc = "Loop"
  /\ Len(stack) = 0
  /\ A' = A
  /\ A0' = A0
  /\ stack' = stack
  /\ pc' = "Done"
  \/
  /\ pc = "Loop"
  /\ Len(stack) > 0
  /\ LET fr == stack[Len(stack)] IN
       IF fr.l >= fr.r
       THEN
         /\ A' = A
         /\ A0' = A0
         /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
         /\ pc' = "Loop"
       ELSE
         /\ \E p \in fr.l..(fr.r - 1), A2 \in [Indices -> Val] :
              /\ PermuteWithin(A, A2, fr.l, fr.r)
              /\ PartitionedAt(A2, fr.l, fr.r, p)
              /\ A' = A2
              /\ A0' = A0
              /\ stack' =
                   Append(
                     Append(SubSeq(stack, 1, Len(stack) - 1),
                            [l |-> fr.l, r |-> p]),
                     [l |-> p + 1, r |-> fr.r]
                   )
              /\ pc' = "Loop"

vars == << A, A0, stack, pc >>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================