---------------------------- MODULE PrimeScoping ----------------------------
EXTENDS Naturals

VARIABLES x, y, ok

vars == <<x, y, ok>>

(***************************************************************************)
(* Operators used to exercise the semantics of the prime operator.        *)
(***************************************************************************)

\* 1. Prime inside an operator definition
PrimedX == x'

\* 2. Operator whose body mentions state variables (to be primed as a whole)
SumXY == x + y

\* 3. Operator taking a parameter
Inc(a) == a + 1

\* 3b. Operator priming its own parameter
PrimeParam(a) == a'

\* 5. Operator combining a state variable with a parameter
AddX(p) == x + p

\* Operator combining both variables and a parameter
Mix(p) == (x * 2) + y + p

(***************************************************************************)
(* Test cases: each must evaluate to TRUE in a step where x' and y' are   *)
(* already determined.                                                    *)
(***************************************************************************)

\* 1. Priming inside an operator definition refers to the next state
Test1 == PrimedX = x'

\* 2. Priming an entire operator application evaluates its body in the
\*    next state
Test2 == /\ SumXY' = x' + y'
         /\ (SumXY)' = SumXY'

\* 3. Priming an operator application with a variable argument versus
\*    priming the argument before passing it
Test3 == /\ Inc(x)' = x' + 1
         /\ Inc(x') = x' + 1
         /\ Inc(x)' = Inc(x')
         /\ Inc(x) = x + 1
         /\ PrimeParam(x) = x'
         /\ PrimeParam(y) = y'

\* 4. Priming LET-bound names versus priming the original expression
Test4 == /\ LET z == x + 1 IN z' = x' + 1
         /\ LET z == x + 1 IN z' = (x + 1)'
         /\ LET z == x + 1 IN z = x + 1
         /\ LET z == x' IN z = x'
         /\ (LET z == x IN z + y)' = x' + y'

\* 5. Priming operator applications with arguments affects only the state
\*    variables, not constant parameter values
Test5 == /\ AddX(10)' = x' + 10
         /\ \A c \in {0, 1, 2} : AddX(c)' = x' + c
         /\ \A c \in {0, 1, 2} : Mix(c)' = (x' * 2) + y' + c
         /\ LET p == 7 IN AddX(p)' = x' + 7
         /\ AddX(x)' = x' + x'
         /\ AddX(y)' = x' + y'

\* 6. Nested LET with locally defined operators
Test6 == /\ LET F(a) == a + x IN F(y)' = y' + x'
         /\ LET F(a) == a + x IN F(3)' = 3 + x'
         /\ LET F(a) == a + x
                G(b) == F(b) + y
            IN  G(1)' = 1 + x' + y'
         /\ LET F(a) == a + x
            IN  LET H == F(y)
                IN  /\ H' = y' + x'
                    /\ H  = y + x
         /\ LET P(a) == a'
            IN  P(x + y) = x' + y'

AllTests == Test1 /\ Test2 /\ Test3 /\ Test4 /\ Test5 /\ Test6

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)

Init == /\ x = 0
        /\ y = 0
        /\ ok = TRUE

Next == /\ x' = IF x < 5 THEN x + 1 ELSE 0
        /\ y' = (x + 2) % 4
        /\ ok' = (ok /\ AllTests)

Spec == Init /\ [][Next]_vars

TypeOK == /\ x \in 0..5
          /\ y \in 0..3
          /\ ok \in BOOLEAN

Inv == /\ TypeOK
       /\ ok = TRUE

=============================================================================