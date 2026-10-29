------------------------------ MODULE MergeSort ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS N, ArrayLen

ASSUME N \in Nat \ {0}
ASSUME ArrayLen \in Nat

Values == 1..N

AllArrays == UNION { [1..L -> Values] : L \in 0..ArrayLen }

defaultInitValue == 0

VARIABLES a, b, pc, stack, lo, hi, mid, i, j, k

vars == << a, b, pc, stack, lo, hi, mid, i, j, k >>

Init ==
    /\ a \in AllArrays
    /\ b = a
    /\ stack = << >>
    /\ lo = defaultInitValue
    /\ hi = defaultInitValue
    /\ mid = defaultInitValue
    /\ i = defaultInitValue
    /\ j = defaultInitValue
    /\ k = defaultInitValue
    /\ pc = "main"

\* main: call mergesort(1, Len(a))
main ==
    /\ pc = "main"
    /\ stack' = << [ procedure |-> "mergesort",
                     pc        |-> "Done",
                     lo        |-> lo,
                     hi        |-> hi,
                     mid       |-> mid,
                     i         |-> i,
                     j         |-> j,
                     k         |-> k ] >> \o stack
    /\ lo' = 1
    /\ hi' = Len(a)
    /\ mid' = defaultInitValue
    /\ i' = defaultInitValue
    /\ j' = defaultInitValue
    /\ k' = defaultInitValue
    /\ pc' = "ms1"
    /\ UNCHANGED << a, b >>

\* ms1: if lo < hi then mid := (lo+hi) \div 2; call mergesort(lo, mid)
ms1 ==
    /\ pc = "ms1"
    /\ IF lo < hi
         THEN LET m == (lo + hi) \div 2 IN
              /\ stack' = << [ procedure |-> "mergesort",
                               pc        |-> "ms2",
                               lo        |-> lo,
                               hi        |-> hi,
                               mid       |-> m,
                               i         |-> i,
                               j         |-> j,
                               k         |-> k ] >> \o stack
              /\ lo' = lo
              /\ hi' = m
              /\ mid' = defaultInitValue
              /\ i' = defaultInitValue
              /\ j' = defaultInitValue
              /\ k' = defaultInitValue
              /\ pc' = "ms1"
         ELSE /\ pc' = "ret"
              /\ UNCHANGED << stack, lo, hi, mid, i, j, k >>
    /\ UNCHANGED << a, b >>

\* ms2: call mergesort(mid+1, hi)
ms2 ==
    /\ pc = "ms2"
    /\ stack' = << [ procedure |-> "mergesort",
                     pc        |-> "ms3",
                     lo        |-> lo,
                     hi        |-> hi,
                     mid       |-> mid,
                     i         |-> i,
                     j         |-> j,
                     k         |-> k ] >> \o stack
    /\ lo' = mid + 1
    /\ hi' = hi
    /\ mid' = defaultInitValue
    /\ i' = defaultInitValue
    /\ j' = defaultInitValue
    /\ k' = defaultInitValue
    /\ pc' = "ms1"
    /\ UNCHANGED << a, b >>

\* ms3: copy a[lo..hi] into buffer b, initialize merge indices
ms3 ==
    /\ pc = "ms3"
    /\ b' = [x \in DOMAIN a |-> IF x \in lo..hi THEN a[x] ELSE b[x]]
    /\ i' = lo
    /\ j' = mid + 1
    /\ k' = lo
    /\ pc' = "mloop"
    /\ UNCHANGED << a, stack, lo, hi, mid >>

\* mloop: merge b[lo..mid] and b[mid+1..hi] back into a[lo..hi]
mloop ==
    /\ pc = "mloop"
    /\ IF k <= hi
         THEN /\ IF i <= mid /\ (j > hi \/ b[i] <= b[j])
                   THEN /\ a' = [a EXCEPT ![k] = b[i]]
                        /\ i' = i + 1
                        /\ j' = j
                   ELSE /\ a' = [a EXCEPT ![k] = b[j]]
                        /\ j' = j + 1
                        /\ i' = i
              /\ k' = k + 1
              /\ pc' = "mloop"
         ELSE /\ pc' = "ret"
              /\ UNCHANGED << a, i, j, k >>
    /\ UNCHANGED << b, stack, lo, hi, mid >>

\* ret: return from procedure mergesort
ret ==
    /\ pc = "ret"
    /\ stack # << >>
    /\ pc' = Head(stack).pc
    /\ lo' = Head(stack).lo
    /\ hi' = Head(stack).hi
    /\ mid' = Head(stack).mid
    /\ i' = Head(stack).i
    /\ j' = Head(stack).j
    /\ k' = Head(stack).k
    /\ stack' = Tail(stack)
    /\ UNCHANGED << a, b >>

mergesort == ms1 \/ ms2 \/ ms3 \/ mloop \/ ret

\* Allow infinite stuttering to prevent deadlock on termination.
Terminating == pc = "Done" /\ UNCHANGED vars

Next == main \/ mergesort \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Properties

TypeOK ==
    /\ a \in AllArrays
    /\ b \in AllArrays
    /\ DOMAIN b = DOMAIN a
    /\ pc \in {"main", "ms1", "ms2", "ms3", "mloop", "ret", "Done"}
    /\ stack \in Seq([ procedure : {"mergesort"},
                       pc        : {"ms2", "ms3", "Done"},
                       lo        : Int,
                       hi        : Int,
                       mid       : Int,
                       i         : Int,
                       j         : Int,
                       k         : Int ])

Sorted(arr) == \A x, y \in DOMAIN arr : x < y => arr[x] <= arr[y]

\* Safety: when the algorithm finishes, the array is sorted.
SortedWhenDone == (pc = "Done") => Sorted(a)

\* Liveness: the algorithm terminates.
Termination == <>(pc = "Done")

=============================================================================