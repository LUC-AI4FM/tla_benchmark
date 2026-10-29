---- MODULE PrimeTest ----
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Init == /\ PrintT("Should find 2 distinct states")
        /\ x = 1
        /\ y = 1

TNext == /\ x' = x + 1
         /\ x' = 2
         /\ \/ y' = y
            \* Test 2: primed expression evaluated in a conditional guard
            \/ /\ x' = 2
               /\ y' = 1
            \* Test 3: guard should never be satisfiable
            \/ /\ x' # 2
               /\ Assert(FALSE, "Test 3 failed: x' # 2 should be false")
               /\ y' = y

\* Additional tests (commented out) for primed expressions in
\* conditionals, set constructions, function applications, and
\* operator definitions:
\*   \/ y' = IF x' = 2 THEN 1 ELSE 2
\*   \/ y' \in {z \in {1, 2} : z = x' - 1}
\*   \/ y' = [i \in {1} |-> x' - 1][1]
\*   \/ LET Op(a) == a - 1 IN y' = Op(x')

Next == \/ TNext
        \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

Inv == TRUE

TypeOK == /\ x \in {1, 2}
          /\ y = 1

====