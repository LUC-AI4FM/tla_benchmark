---------------------------- MODULE mergesort ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS ArrayLen, defaultInitValue

ASSUME ArrayLen \in Nat /\ ArrayLen >= 0

VARIABLES array, pc, stack, aux, initialArray

vars == <<array, pc, stack, aux, initialArray>>

\* Helper: Convert sequence to multiset (bag)
SeqToMultiset(s) ==
    [e \in DOMAIN s |-> Cardinality({i \in DOMAIN s : s[i] = s[e]})]

BagEqual(s1, s2) ==
    /\ DOMAIN s1 = DOMAIN s2
    /\ \A i \in DOMAIN s1 : s1[i] = s2[i]

\* Count occurrences of element e in sequence s
Count(e, s) ==
    Cardinality({i \in DOMAIN s : s[i] = e})

\* Check if two sequences have same multiset of elements
SameMultiset(s1, s2) ==
    \A e \in Int : Count(e, s1) = Count(e, s2)

\* Check if sequence is sorted (nondecreasing)
IsSorted(s) ==
    \A i, j \in DOMAIN s : i < j => s[i] <= s[j]

\* Check if a range [lo, hi] in array is sorted
RangeIsSorted(arr, lo, hi) ==
    \A i, j \in lo..hi : i < j => arr[i] <= arr[j]

\* Extract subsequence from lo to hi
SubSeq(s, lo, hi) ==
    IF lo > hi THEN << >>
    ELSE [i \in 1..(hi - lo + 1) |-> s[lo + i - 1]]

\* Merge operation specification: given two sorted adjacent ranges, produce sorted combination
\* This is specified declaratively - the result must be sorted and preserve multiset
MergeSpec(arr, lo, mid, hi) ==
    LET leftPart == SubSeq(arr, lo, mid)
        rightPart == SubSeq(arr, mid + 1, hi)
        combined == leftPart \o rightPart
    IN {newArr \in [1..Len(arr) -> Int] :
        /\ \A i \in 1..Len(arr) : 
            (i < lo \/ i > hi) => newArr[i] = arr[i]
        /\ RangeIsSorted(newArr, lo, hi)
        /\ SameMultiset(SubSeq(newArr, lo, hi), combined)}

\* Stack frame for recursive calls: <<lo, hi, phase>>
\* phase = "divide" means we need to split
\* phase = "left" means left half is being processed
\* phase = "right" means right half is being processed  
\* phase = "merge" means both halves done, need to merge

\* Initial state: array can be any sequence of integers of length ArrayLen
Init ==
    /\ array \in [1..ArrayLen -> Int]
    /\ initialArray = array
    /\ pc = "running"
    /\ stack = IF ArrayLen <= 1 
               THEN << >> 
               ELSE << <<1, ArrayLen, "divide">> >>
    /\ aux = << >>

\* Divide step: push two recursive calls for left and right halves
Divide ==
    /\ pc = "running"
    /\ stack # << >>
    /\ LET frame == Head(stack)
           lo == frame[1]
           hi == frame[2]
           phase == frame[3]
       IN /\ phase = "divide"
          /\ IF hi - lo < 1
             THEN \* Base case: single element or empty, already sorted
                  /\ stack' = Tail(stack)
                  /\ UNCHANGED <<array, aux, initialArray, pc>>
             ELSE \* Split into halves
                  LET mid == (lo + hi) \div 2
                  IN /\ stack' = << <<lo, mid, "divide">>, 
                                    <<mid + 1, hi, "divide">>,
                                    <<lo, hi, "merge">> >> \o Tail(stack)
                     /\ UNCHANGED <<array, aux, initialArray, pc>>

\* Merge step: merge two sorted halves
Merge ==
    /\ pc = "running"
    /\ stack # << >>
    /\ LET frame == Head(stack)
           lo == frame[1]
           hi == frame[2]
           phase == frame[3]
       IN /\ phase = "merge"
          /\ LET mid == (lo + hi) \div 2
                 possibleResults == MergeSpec(array, lo, mid, hi)
             IN /\ possibleResults # {}
                /\ \E newArr \in possibleResults :
                     /\ array' = newArr
                     /\ stack' = Tail(stack)
                     /\ UNCHANGED <<aux, initialArray, pc>>

\* Check for termination
CheckDone ==
    /\ pc = "running"
    /\ stack = << >>
    /\ pc' = "done"
    /\ UNCHANGED <<array, stack, aux, initialArray>>

\* Combined next state relation
Next ==
    \/ Divide
    \/ Merge
    \/ CheckDone

\* Fairness: ensure progress
Fairness ==
    /\ WF_vars(Divide)
    /\ WF_vars(Merge)
    /\ WF_vars(CheckDone)

\* Complete specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: when done, array is sorted
Sorted ==
    pc = "done" => IsSorted(array)

\* Preservation: multiset is preserved throughout
Preserved ==
    SameMultiset(array, initialArray)

\* Combined invariant
Invariant ==
    /\ Preserved
    /\ (pc = "done" => IsSorted(array))

\* Termination: eventually reaches done state
Termination == <>(pc = "done")

\* Type invariant for model checking
TypeOK ==
    /\ array \in [1..ArrayLen -> Int]
    /\ initialArray \in [1..ArrayLen -> Int]
    /\ pc \in {"running", "done"}

=========================================================================