------------------------------ MODULE LeastRotation ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharSetSize,      \* number of symbols in the alphabet
          MaxStringLength,  \* bound on the length of input strings
          CharacterSet      \* the alphabet (overridden by MCCharacterSet)

ASSUME CharSetSize \in Nat /\ CharSetSize >= 1
ASSUME MaxStringLength \in Nat

\* Concrete alphabet used for model checking: symbols 1..CharSetSize,
\* ordered by the standard numeric order.
MCCharacterSet == 1..CharSetSize

\* All strings over the alphabet of length at most MaxStringLength
Strings == UNION { [1..n -> CharacterSet] : n \in 0..MaxStringLength }

\* Circular rotation of s by k positions to the left (0-based index k)
Rotate(s, k) ==
    [i \in 1..Len(s) |-> s[((i - 1 + k) % Len(s)) + 1]]

\* Strict lexicographic order on strings of equal length
LexLess(a, b) ==
    \E j \in 1..Len(a) :
        /\ \A m \in 1..(j - 1) : a[m] = b[m]
        /\ a[j] < b[j]

LexLeq(a, b) == a = b \/ LexLess(a, b)

\* Valid rotation indices for a string
Indices(s) == IF Len(s) = 0 THEN {0} ELSE 0..(Len(s) - 1)

\* Specification-level (non-algorithmic) least rotation: smallest index
\* among all indices whose rotation is minimal.
IsLeast(s, i) ==
    /\ i \in Indices(s)
    /\ \A j \in Indices(s) : LexLeq(Rotate(s, i), Rotate(s, j))
    /\ \A j \in Indices(s) : j < i => LexLess(Rotate(s, i), Rotate(s, j))

VARIABLES str,     \* the input string
          best,    \* current best (least) rotation index
          k,       \* next candidate index to examine
          done,    \* has the algorithm terminated?
          result   \* the output rotated string

vars == << str, best, k, done, result >>

Init ==
    /\ str \in Strings
    /\ best = 0
    /\ k = 1
    /\ done = FALSE
    /\ result = << >>

\* Compare candidate rotation k with the current best; strictly-less test
\* guarantees that the smallest index among equal rotations is kept.
Step ==
    /\ ~done
    /\ k < Len(str)
    /\ best' = IF LexLess(Rotate(str, k), Rotate(str, best)) THEN k ELSE best
    /\ k' = k + 1
    /\ UNCHANGED << str, done, result >>

Finish ==
    /\ ~done
    /\ k >= Len(str)
    /\ done' = TRUE
    /\ result' = Rotate(str, best)
    /\ UNCHANGED << str, best, k >>

Terminated ==
    /\ done
    /\ UNCHANGED vars

Next == Step \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ Finish)

-----------------------------------------------------------------------------

TypeInvariant ==
    /\ str \in Strings
    /\ best \in 0..MaxStringLength
    /\ best \in Indices(str)
    /\ k \in 1..(MaxStringLength + 1)
    /\ done \in BOOLEAN
    /\ result \in Strings
    /\ \A i \in 1..Len(result) : result[i] \in CharacterSet

\* Loop invariant: best is the least (canonical) rotation among 0..k-1
LoopInvariant ==
    ~done =>
        /\ \A j \in 0..(k - 1) :
              j \in Indices(str) => LexLeq(Rotate(str, best), Rotate(str, j))
        /\ \A j \in 0..(best - 1) : LexLess(Rotate(str, best), Rotate(str, j))

Correctness ==
    /\ LoopInvariant
    /\ done =>
         /\ best \in Indices(str)
         /\ Len(result) = Len(str)
         /\ result = Rotate(str, best)
         \* Minimality
         /\ \A j \in Indices(str) : LexLeq(result, Rotate(str, j))
         \* Canonicality: smallest index among equal minimal rotations
         /\ \A j \in Indices(str) : j < best => result # Rotate(str, j)
         /\ IsLeast(str, best)
         \* Identity rotation for trivial strings
         /\ Len(str) <= 1 => (best = 0 /\ result = str)
         \* Safety: symbols remain in the alphabet
         /\ \A i \in 1..Len(result) : result[i] \in CharacterSet

\* Termination: the algorithm always produces a result
Termination == <>done

THEOREM Spec => [](TypeInvariant /\ Correctness)
=============================================================================