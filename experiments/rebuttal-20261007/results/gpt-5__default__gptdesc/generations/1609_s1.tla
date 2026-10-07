----------------------------- MODULE RecursiveQuickSort -----------------------------
EXTENDS Naturals, Integers, FiniteSets, Sequences

(*
--algorithm QuickSort
variables 
  \* The array of integers to sort:
  arr \in [1..ArrayLen -> Int];

procedure QS(l, r)
{ QSBody:
  if l < r then
    with p \in l..(r-1) do
      \* Nondeterministically choose a new array that is a permutation
      \* of arr on l..r, preserves elements outside l..r, and partitions
      \* around p so that all entries at/before p are <= all entries after p.
      with arr2 \in [1..ArrayLen -> Int] do
        if IsPermExcept(arr, arr2, l, r) /\ Partitioned(arr2, l, p, r) then
          arr := arr2;
          call QS(l, p);
          call QS(p+1, r);
        end if;
      end with;
    end with;
  end if;
  return;
}

begin
  call QS(1, ArrayLen);
Done:
  skip;
end algorithm
*)

CONSTANTS ArrayLen

ASSUME ArrayLen \in Nat \ {0}

VARIABLES 
  arr,      \* current array
  AInit,    \* snapshot of the initial array
  stack,    \* sequence of frames [lo |-> ..., hi |-> ...]
  pc        \* control state: "Start", "Step", "Done"

vars == << arr, AInit, stack, pc >>

Domain == 1..ArrayLen

Frames ==
  { f \in [lo : Domain, hi : Domain] : f.lo \in Domain /\ f.hi \in Domain /\ f.lo <= f.hi }

StackOK ==
  /\ stack \in Seq(Frames)

Top(s) == s[Len(s)]
ButLast(s) == SubSeq(s, 1, Len(s) - 1)

CountRange(a, l, h, v) ==
  Cardinality({ i \in l..h : a[i] = v })

PermutesRange(a1, a2, l, h) ==
  \A v \in Int : CountRange(a1, l, h, v) = CountRange(a2, l, h, v)

PermutesAll(a1, a2) ==
  \A v \in Int : CountRange(a1, 1, ArrayLen, v) = CountRange(a2, 1, ArrayLen, v)

IsPermExcept(aOld, aNew, l, h) ==
  /\ \A i \in Domain :
       IF i < l \/ i > h THEN aNew[i] = aOld[i] ELSE TRUE
  /\ PermutesRange(aOld, aNew, l, h)

Partitioned(a, l, p, h) ==
  /\ l <= p /\ p < h
  /\ \A i \in l..p : \A j \in (p+1)..h : a[i] <= a[j]

Sorted(a) ==
  \A i, j \in Domain : (i < j) => a[i] <= a[j]

TypeOK ==
  /\ arr \in [Domain -> Int]
  /\ AInit \in [Domain -> Int]
  /\ StackOK
  /\ pc \in {"Start", "Step", "Done"}

Init ==
  /\ arr \in [Domain -> Int]
  /\ AInit = arr
  /\ stack = << >>
  /\ pc = "Start"

StartStep ==
  /\ pc = "Start"
  /\ stack' = << [lo |-> 1, hi |-> ArrayLen] >>
  /\ pc' = "Step"
  /\ UNCHANGED << arr, AInit >>

StepDone ==
  /\ pc = "Step"
  /\ Len(stack) = 0
  /\ pc' = "Done"
  /\ UNCHANGED << arr, AInit, stack >>

StepWork ==
  /\ pc = "Step"
  /\ Len(stack) > 0
  /\ LET f == Top(stack) IN
     LET rest == ButLast(stack) IN
       \/ /\ f.lo >= f.hi
          /\ stack' = rest
          /\ UNCHANGED << arr, AInit, pc >>
       \/ /\ f.lo < f.hi
          /\ \E p \in f.lo..(f.hi - 1) :
               \E arr2 \in [Domain -> Int] :
                 /\ IsPermExcept(arr, arr2, f.lo, f.hi)
                 /\ Partitioned(arr2, f.lo, p, f.hi)
                 /\ arr' = arr2
                 /\ stack' =
                      Append(
                        Append(rest, [lo |-> f.lo,    hi |-> p]),
                               [lo |-> p + 1, hi |-> f.hi]
                      )
                 /\ UNCHANGED << AInit, pc >>

Next ==
  \/ StartStep
  \/ StepDone
  \/ StepWork

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

PermInv ==
  PermutesAll(arr, AInit)

SafetyInv ==
  /\ TypeOK
  /\ PermInv

Termination ==
  <> (pc = "Done")

FinalOK ==
  (pc = "Done") => (PermutesAll(arr, AInit) /\ Sorted(arr))

THEOREM TerminationUnderSpec ==
  Spec => Termination

THEOREM FinalCorrectness ==
  Spec => []FinalOK
====================================================================================