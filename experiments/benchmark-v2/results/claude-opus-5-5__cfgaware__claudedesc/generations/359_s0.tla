---------------------------- MODULE PrimeTest ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

Init == /\ PrintT("Should find 2 distinct states")
        /\ x = 1
        /\ y = 1

TNext == /\ x' = x + 1
         /\ x' = 2
         /\ \/ y' = y
            \* Test 2: primed expression in a guard evaluates correctly
            \/ /\ IF x' = 2 THEN y' = 1 ELSE y' = 0
            \* Test 3: guard should never be satisfiable
            \/ /\ x' # 2
               /\ Assert(FALSE, "Test 3 Failed: x' # 2 should be unsatisfiable")
               /\ y' = y
            \* Test 4 (disabled): primed expression in set construction
            \* \/ y' \in {z \in {x'} : z = 2}
            \* Test 5 (disabled): primed expression in function application
            \* \/ y' = [i \in {1, 2} |-> i][x']
            \* Test 6 (disabled): primed expression in operator definition
            \* \/ LET Op(a) == a' IN y' = Op(y)

Next == \/ TNext
        \/ UNCHANGED <<x, y>>

Inv == TRUE

=============================================================================