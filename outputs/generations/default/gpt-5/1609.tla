------------------------------ MODULE Quicksort ------------------------------

EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS
  ArrayLen,
  Values

ASSUME
  /\ ArrayLen \in Nat
  /\ Values \subseteq Int

(*
PlusCal sketch (commented):
--algorithm QS
variables A \in [0..ArrayLen-1 -> Values], A0 = A;
{
  procedure QS(l, r)
  {
    if (l < r) {
      with pv \in l..r do
        with Anew \in [0..ArrayLen-1 -> Values] do
          assume
            /\ \A i \in (0..ArrayLen-1) \ (l..r): Anew[i] = A[i]
            /\ \A v \in Values:
                 Cardinality({ i \in (0..ArrayLen-1) : l <= i /\ i <= r /\ Anew[i] = v })
               = Cardinality({ i \in (0..ArrayLen-1) : l <= i /\ i <= r /\ A[i] = v })
            /\ \A i \in (0..ArrayLen-1) \cap (l..pv):
               \A j \in (0..ArrayLen-1) \cap ((pv+1)..r): Anew[i] <= Anew[j];
          end with;
          A := Anew;
      end with;
      call QS(l, pv);
      call QS(pv+1, r);
    }
  }
  { call QS(0, ArrayLen-1); }
}
*)

CONSTANTS

VARIABLES
  A,    \* current array: function from indices to Values
  A0,   \* initial array snapshot
  stack,\* sequence of frames encoding recursion
  pc    \* control state (program counter)

Indices == 0..(ArrayLen - 1)

Stage == {"enter", "afterPart", "afterLeft"}

Frames == [l : Int, r : Int, stage : Stage, p : Int]

Top(s) == s[Len(s)]

PopLast(s) == SubSeq(s, 1, Len(s) - 1)

ReplaceTop(s, e) == [s EXCEPT ![Len(s)] = e]

CountRange(arr, l, r, v) ==
  Cardinality({ i \in Indices : (l <= i) /\ (i <= r) /\ arr[i] = v })

PermutationWithin(Anew, Aold, l, r) ==
  /\ \A i \in (Indices \ (l..r)) : Anew[i] = Aold[i]
  /\ \A v \in Values : CountRange(Anew, l, r, v) = CountRange(Aold, l, r, v)

Partitioned(Anew, l, pv, r) ==
  \A i \in (Indices \cap (l..pv)) :
    \A j \in (Indices \cap ((pv+1)..r)) : Anew[i] <= Anew[j]

Permutation(A1, A2) ==
  \A v \in Values :
    Cardinality({ i \in Indices : A1[i] = v })
  = Cardinality({ i \in Indices : A2[i] = v })

Sorted(arr) ==
  \A i, j \in Indices : (i <= j) => arr[i] <= arr[j]

SeqItems(s) == { s[i] : i \in 1..Len(s) }

TypeOK ==
  /\ A \in [Indices -> Values]
  /\ A0 \in [Indices -> Values]
  /\ pc \in {"Start", "Dispatch", "ChoosePartition", "PushLeft", "PushRight", "Done"}
  /\ stack \in Seq(Frames)
  /\ \A f \in SeqItems(stack) :
       IF f.stage \in {"afterPart", "afterLeft"} THEN
         /\ f.l \in Int /\ f.r \in Int /\ f.p \in Int
         /\ f.l \in Indices /\ f.r \in Indices
         /\ f.l <= f.p /\ f.p <= f.r
       ELSE
         /\ f.l \in Int /\ f.r \in Int /\ f.p \in Int

Init ==
  /\ A \in [Indices -> Values]
  /\ A0 = A
  /\ stack = << >>
  /\ pc = "Start"

StartAct ==
  /\ pc = "Start"
  /\ stack' = Append(<< >>, [l |-> 0, r |-> ArrayLen - 1, stage |-> "enter", p |-> -1])
  /\ pc' = "Dispatch"
  /\ UNCHANGED << A, A0 >>

DoneAct ==
  /\ pc = "Dispatch"
  /\ Len(stack) = 0
  /\ pc' = "Done"
  /\ UNCHANGED << A, A0, stack >>

BaseCaseAct ==
  /\ pc = "Dispatch"
  /\ Len(stack) > 0
  /\ LET fr == Top(stack) IN fr.stage = "enter" /\ fr.l >= fr.r
  /\ stack' = PopLast(stack)
  /\ pc' = "Dispatch"
  /\ UNCHANGED << A, A0 >>

ToPartitionAct ==
  /\ pc = "Dispatch"
  /\ Len(stack) > 0
  /\ LET fr == Top(stack) IN fr.stage = "enter" /\ fr.l < fr.r
  /\ pc' = "ChoosePartition"
  /\ UNCHANGED << A, A0, stack >>

ToPushLeftAct ==
  /\ pc = "Dispatch"
  /\ Len(stack) > 0
  /\ LET fr == Top(stack) IN fr.stage = "afterPart"
  /\ pc' = "PushLeft"
  /\ UNCHANGED << A, A0, stack >>

ToPushRightAct ==
  /\ pc = "Dispatch"
  /\ Len(stack) > 0
  /\ LET fr == Top(stack) IN fr.stage = "afterLeft"
  /\ pc' = "PushRight"
  /\ UNCHANGED << A, A0, stack >>

PartitionAct ==
  /\ pc = "ChoosePartition"
  /\ LET k == Len(stack) IN
     LET fr == stack[k] IN
       /\ fr.stage = "enter"
       /\ fr.l < fr.r
       /\ \E pv \in (Indices \cap (fr.l..fr.r)),
            Anew \in [Indices -> Values] :
            /\ PermutationWithin(Anew, A, fr.l, fr.r)
            /\ Partitioned(Anew, fr.l, pv, fr.r)
            /\ A' = Anew
            /\ stack' = [stack EXCEPT ![k] = [l |-> fr.l, r |-> fr.r, stage |-> "afterPart", p |-> pv]]
            /\ pc' = "Dispatch"
            /\ UNCHANGED A0

PushLeftAct ==
  /\ pc = "PushLeft"
  /\ LET k == Len(stack) IN
     LET fr == stack[k] IN
       /\ fr.stage = "afterPart"
       /\ stack' =
            Append(
              [stack EXCEPT ![k] = [l |-> fr.l, r |-> fr.r, stage |-> "afterLeft", p |-> fr.p]],
              [l |-> fr.l, r |-> fr.p, stage |-> "enter", p |-> -1]
            )
       /\ pc' = "Dispatch"
       /\ UNCHANGED << A, A0 >>

PushRightAct ==
  /\ pc = "PushRight"
  /\ LET k == Len(stack) IN
     LET fr == stack[k] IN
       /\ fr.stage = "afterLeft"
       /\ stack' =
            Append(
              PopLast(stack),
              [l |-> fr.p + 1, r |-> fr.r, stage |-> "enter", p |-> -1]
            )
       /\ pc' = "Dispatch"
       /\ UNCHANGED << A, A0 >>

Next ==
  \/ StartAct
  \/ DoneAct
  \/ BaseCaseAct
  \/ ToPartitionAct
  \/ ToPushLeftAct
  \/ ToPushRightAct
  \/ PartitionAct
  \/ PushLeftAct
  \/ PushRightAct

vars == << A, A0, stack, pc >>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

FinalOK == (pc = "Done") => (Permutation(A, A0) /\ Sorted(A))

THEOREM Spec => []TypeOK

THEOREM Spec => Termination

THEOREM Spec => []FinalOK

=============================================================================