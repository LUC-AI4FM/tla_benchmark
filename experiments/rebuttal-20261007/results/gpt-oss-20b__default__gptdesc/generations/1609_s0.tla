MODULE QuickSort

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS ArrayLen, InitArray

VARIABLES arr, stack, pc

(* Helper functions *)

Count(v, seq) ==
  Len({i \in 1..Len(seq) : seq[i] = v})

SubSeq(seq, i, j) ==
  [k \in 1..(j - i + 1) -> seq[i + k - 1]]

PermutationWithin(a,b,i,j) ==
  \A v \in DOMAIN a :
    Count(v, SubSeq(a, i, j)) = Count(v, SubSeq(b, i, j))

PartitionProperty(arr', low, high, p) ==
  (\A i \in [low..p] : arr'[i] <= arr'[p]) /\
  (\A j \in [p+1..high] : arr'[j] > arr'[p])

(* Invariants *)

PermutationInvariant == 
  \A v \in DOMAIN InitArray :
    Count(v, InitArray) = Count(v, arr)

SortedInvariant ==
  \A i \in 1..(ArrayLen-1) : arr[i] <= arr[i+1]

(* Initial state *)
Init ==
  /\ arr = InitArray
  /\ stack = <<>>
  /\ pc = "Init"

(* Next action *)
Next ==
  \/ pc = "Init" /\
     arr' = InitArray /\
     stack' = << [low |-> 1, high |-> ArrayLen] >> /\
     pc' = "QS"

  \/ pc = "QS" /\ 
     stack # <<>> /\
     LET
       f == Head(stack)
       low == f.low
       high == f.high
       newStack ==
         IF low >= high THEN
            Tail(stack)
         ELSE
            \E p \in [low..high] :
              \E arr'' \in {arr'': 
                  (\A i \in 1..ArrayLen : (i < low \/ i > high) => arr''[i] = arr[i]) /\
                  PermutationWithin(arr, arr'', low, high) /\ 
                  PartitionProperty(arr'', low, high, p)
              } :
                arr' = arr'' /\ 
                Tail(stack) \o
                  (IF low <= p-1 THEN << [low |-> low, high |-> p-1] >> ELSE <<>> ENDIF) \o
                  (IF p+1 <= high THEN << [low |-> p+1, high |-> high] >> ELSE <<>> ENDIF)
         fi
     IN
       stack' == newStack /\ pc' == IF newStack = <<>> THEN "Done" ELSE "QS" ENDIF

  \/ pc = "Done" /\ TRUE

(* Specification with weak fairness on Next *)
Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

(* Properties *)

Termination == <> (pc = "Done")

InvariantProps == 
  [] PermutationInvariant /\
  [] (pc = "Done" => SortedInvariant)

END QuickSort