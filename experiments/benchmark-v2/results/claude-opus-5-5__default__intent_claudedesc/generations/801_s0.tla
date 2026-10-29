------------------------- MODULE LeastCircularSubstring -------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS AlphabetSize, MaxLength

ASSUME AlphabetSize \in Nat \ {0}
ASSUME MaxLength \in Nat \ {0}

Chars == 0 .. (AlphabetSize - 1)

Strings == UNION { [1 .. n -> Chars] : n \in 1 .. MaxLength }

Min(a, b) == IF a <= b THEN a ELSE b

CharAt(str, x) == str[(x % Len(str)) + 1]

Rotation(str, r) == [p \in 1 .. Len(str) |-> str[((r + p - 1) % Len(str)) + 1]]

LexLeq(a, b) ==
    \/ a = b
    \/ \E p \in 1 .. Len(a) :
          /\ \A q \in 1 .. (p - 1) : a[q] = b[q]
          /\ a[p] < b[p]

IsMinimalRotation(str, r) ==
    \A r2 \in 0 .. (Len(str) - 1) : LexLeq(Rotation(str, r), Rotation(str, r2))

LeastMinimalIndex(str) ==
    CHOOSE r \in 0 .. (Len(str) - 1) :
        /\ IsMinimalRotation(str, r)
        /\ \A r2 \in 0 .. (r - 1) : ~IsMinimalRotation(str, r2)

VARIABLES s, i, j, k, result, pc

vars == << s, i, j, k, result, pc >>

TypeOK ==
    /\ s \in Strings
    /\ i \in 0 .. (2 * MaxLength)
    /\ j \in 0 .. (2 * MaxLength + 1)
    /\ k \in 0 .. MaxLength
    /\ result \in (0 .. (MaxLength - 1)) \cup {-1}
    /\ pc \in {"loop", "done"}

Init ==
    /\ s \in Strings
    /\ i = 0
    /\ j = 1
    /\ k = 0
    /\ result = -1
    /\ pc = "loop"

Compare ==
    LET n == Len(s)
        a == CharAt(s, i + k)
        b == CharAt(s, j + k)
    IN
    /\ pc = "loop"
    /\ i < n /\ j < n /\ k < n
    /\ IF a = b
         THEN /\ k' = k + 1
              /\ UNCHANGED << i, j >>
         ELSE /\ k' = 0
              /\ IF a > b
                   THEN LET ni == i + k + 1
                        IN /\ i' = ni
                           /\ j' = IF ni = j THEN j + 1 ELSE j
                   ELSE LET nj == j + k + 1
                        IN /\ j' = IF nj = i THEN nj + 1 ELSE nj
                           /\ i' = i
    /\ UNCHANGED << s, result, pc >>

Finish ==
    LET n == Len(s) IN
    /\ pc = "loop"
    /\ ~(i < n /\ j < n /\ k < n)
    /\ result' = Min(i, j)
    /\ pc' = "done"
    /\ UNCHANGED << s, i, j, k >>

Step == Compare \/ Finish

Terminated == pc = "done" /\ UNCHANGED vars

Next == Step \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------

(* Safety: the returned index yields the lexicographically smallest rotation *)
Correctness ==
    pc = "done" =>
        /\ result \in 0 .. (Len(s) - 1)
        /\ IsMinimalRotation(s, result)

(* Determinism: the result is uniquely determined by the input string *)
Determinism ==
    pc = "done" => result = LeastMinimalIndex(s)

(* The input string is never modified *)
InputUnchanged == [][s' = s]_vars

(* Once a result is produced, it never changes *)
ResultStable == [][pc = "done" => (pc' = "done" /\ result' = result)]_vars

(* Liveness: the algorithm terminates on every valid input *)
Termination == <>(pc = "done")

=============================================================================