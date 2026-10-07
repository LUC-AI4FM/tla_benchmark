---------------------------- MODULE QuickSort ----------------------------

EXTENDS Naturals, Integers, Sequences

(*
PlusCal model (informal, for documentation only)

--algorithm QS {
  variables A \in [1..ArrayLen -> Data];

  define Partitioned(A, lo, hi, p) ==
    /\ lo <= p /\ p <= hi
    /\ \A i \in lo..p: \A j \in (p+1)..hi: A[i] <= A[j];

  define PermuteWithin(A, A2, lo, hi) ==
    LET S == (1..ArrayLen) \cap (lo..hi) IN
      /\ \E pi \in [S -> S]:
            /\ pi is a bijection on S
            /\ \A i \in S: A2[i] = A[pi[i]]
      /\ \A k \in (1..ArrayLen) \ S: A2[k] = A[k];

  procedure QS(lo, hi) {
    if hi > lo then
      with p \in lo..hi, A2 \in [1..ArrayLen -> Data] do
        assume Partitioned(A2, lo, hi, p) /\ PermuteWithin(A, A2, lo, hi);
        A := A2;
      end with;
      call QS(lo, p-1);
      call QS(p+1, hi);
    end if;
  }

  { call QS(1, ArrayLen); }
}
*)

CONSTANTS
  ArrayLen,
  Data

VARIABLES
  A,       \* current array: function from 1..ArrayLen to Data
  InitA,   \* initial array snapshot for permutation check
  pc,      \* control location: "Run" or "Done"
  stack    \* sequence of frames (records) for pending QS calls

Indices == 1..ArrayLen

IsFrame(f) ==
  /\ f \in [ {"lo","hi"} -> Int ]
  /\ 0 <= f.hi /\ f.hi <= ArrayLen
  /\ 1 <= f.lo /\ f.lo <= ArrayLen + 1

FramesOK ==
  /\ stack \in Seq([ {"lo","hi"} -> Int ])
  /\ \A i \in 1..Len(stack): IsFrame(stack[i])

Sub(lo, hi) == Indices \cap (lo..hi)

OneToOne(pi, S) == \A x, y \in S: x # y => pi[x] # pi[y]
Onto(pi, S) == { pi[x] : x \in S } = S
BijectionOn(pi, S) == /\ pi \in [S -> S]
                      /\ OneToOne(pi, S)
                      /\ Onto(pi, S)

Partitioned(Arr, lo, hi, p) ==
  /\ lo <= p /\ p <= hi
  /\ \A i \in (lo..p): \A j \in ((p+1)..hi): Arr[i] <= Arr[j]

PermuteWithin(A1, A2, lo, hi) ==
  LET S == Sub(lo, hi) IN
    /\ \E pi \in [S -> S]:
         /\ BijectionOn(pi, S)
         /\ \A i \in S: A2[i] = A1[pi[i]]
    /\ \A k \in Indices \ S: A2[k] = A1[k]

Perm(A1, A2) ==
  \E pi \in [Indices -> Indices]:
    /\ BijectionOn(pi, Indices)
    /\ \A i \in Indices: A1[i] = A2[pi[i]]

Sorted(Arr) ==
  \A i, j \in Indices: i <= j => Arr[i] <= Arr[j]

Init ==
  /\ A \in [Indices -> Data]
  /\ InitA = A
  /\ pc = "Run"
  /\ stack = << [lo |-> 1, hi |-> ArrayLen] >>

StepPop ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET f == stack[Len(stack)] IN f.hi <= f.lo
  /\ A' = A
  /\ stack' = SubSeq(stack, 1, Len(stack)-1)
  /\ pc' = "Run"
  /\ InitA' = InitA

StepPart ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET f == stack[Len(stack)] IN
       /\ f.hi > f.lo
       /\ \E p \in f.lo..f.hi, A2 \in [Indices -> Data]:
            /\ Partitioned(A2, f.lo, f.hi, p)
            /\ PermuteWithin(A, A2, f.lo, f.hi)
            /\ A' = A2
            /\ stack' =
                 Append(
                   Append(SubSeq(stack, 1, Len(stack)-1),
                          << [lo |-> p+1, hi |-> f.hi] >>),
                   << [lo |-> f.lo, hi |-> p-1] >>)
            /\ pc' = "Run"
            /\ InitA' = InitA

StepDone ==
  /\ pc = "Run"
  /\ Len(stack) = 0
  /\ pc' = "Done"
  /\ UNCHANGED << A, InitA, stack >>

Next == StepPop \/ StepPart \/ StepDone

vars == << A, InitA, pc, stack >>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeInv ==
  /\ A \in [Indices -> Data]
  /\ InitA \in [Indices -> Data]
  /\ pc \in {"Run","Done"}
  /\ FramesOK

PermInv == Perm(A, InitA)

PostCondition ==
  (pc = "Done") => (Sorted(A) /\ Perm(A, InitA))

Termination == <> (pc = "Done")

Correctness == <> (pc = "Done" /\ Sorted(A) /\ Perm(A, InitA))

=============================================================================