---------------------------- MODULE BinarySearch ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    MaxLen,     \* maximum length of the sorted sequence (bounded model checking)
    Values      \* finite domain of elements

ASSUME MaxLenAssump == MaxLen \in Nat
ASSUME ValuesAssump == /\ Values \subseteq Int
                       /\ IsFiniteSet(Values)
                       /\ Values # {}

VARIABLES
    seq,        \* the sorted sequence being searched
    target,     \* the value being searched for
    low,        \* lower bound of the current search space (inclusive)
    high,       \* upper bound of the current search space (inclusive)
    result,     \* index where target was found, 0 if not found / not yet found
    done        \* TRUE once the algorithm has terminated

vars == <<seq, target, low, high, result, done>>

-----------------------------------------------------------------------------
(* Helper definitions *)

\* All sequences over Values with length at most MaxLen
BoundedSeqs == UNION { [1..n -> Values] : n \in 0..MaxLen }

IsSorted(s) == \A i, j \in 1..Len(s) : i <= j => s[i] <= s[j]

SortedSeqs == { s \in BoundedSeqs : IsSorted(s) }

\* Target occurs somewhere in the sequence
TargetInSeq == \E i \in 1..Len(seq) : seq[i] = target

\* Overflow-safe midpoint computation
Mid == low + ((high - low) \div 2)

-----------------------------------------------------------------------------
(* Initial state: any sorted sequence, any target value *)

Init ==
    /\ seq \in SortedSeqs
    /\ target \in Values
    /\ low = 1
    /\ high = Len(seq)
    /\ result = 0
    /\ done = FALSE

-----------------------------------------------------------------------------
(* Actions *)

\* One iteration of the binary search loop: compare target to middle element
Step ==
    /\ ~done
    /\ low <= high
    /\ LET m == Mid IN
         IF seq[m] = target
           THEN /\ result' = m
                /\ done' = TRUE
                /\ UNCHANGED <<low, high>>
         ELSE IF seq[m] < target
           THEN /\ low' = m + 1
                /\ UNCHANGED <<high, result, done>>
         ELSE /\ high' = m - 1
              /\ UNCHANGED <<low, result, done>>
    /\ UNCHANGED <<seq, target>>

\* Search space exhausted: target not found
NotFound ==
    /\ ~done
    /\ low > high
    /\ result' = 0
    /\ done' = TRUE
    /\ UNCHANGED <<seq, target, low, high>>

\* Algorithm has terminated; allow stuttering to avoid deadlock
Terminated ==
    /\ done
    /\ UNCHANGED vars

Next == Step \/ NotFound \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ NotFound)

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ seq \in SortedSeqs
    /\ target \in Values
    /\ low \in 1..(MaxLen + 1)
    /\ high \in 0..MaxLen
    /\ result \in 0..MaxLen
    /\ done \in BOOLEAN

\* Soundness: a reported position actually holds the target
Soundness ==
    result # 0 => /\ result \in 1..Len(seq)
                  /\ seq[result] = target

\* Completeness: if the algorithm has terminated and the target exists, it was found
Completeness ==
    (done /\ TargetInSeq) => result # 0

\* Search space invariant: while searching, the target (if present) lies in [low, high]
SearchSpaceInvariant ==
    (~done /\ TargetInSeq) => \E i \in low..high : seq[i] = target

\* Bounds stay within the sequence while searching
BoundsInvariant ==
    ~done => /\ 1 <= low
             /\ high <= Len(seq)
             /\ low <= high + 1

\* Result is only set upon termination
ResultOnlyWhenDone == result # 0 => done

Invariants ==
    /\ TypeOK
    /\ Soundness
    /\ Completeness
    /\ SearchSpaceInvariant
    /\ BoundsInvariant
    /\ ResultOnlyWhenDone

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Termination: the algorithm always eventually terminates
Termination == <>done

\* Once terminated, it stays terminated
StaysDone == [](done => []done)

\* Eventual completeness: if target is present, it is eventually found
EventuallyFound == TargetInSeq => <>(result # 0 /\ seq[result] = target)

-----------------------------------------------------------------------------
THEOREM Spec => []Invariants
THEOREM Spec => Termination
THEOREM Spec => EventuallyFound
=============================================================================