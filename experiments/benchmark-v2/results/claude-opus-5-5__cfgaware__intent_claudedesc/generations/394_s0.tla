---------------------------- MODULE PrimeScoping ----------------------------
EXTENDS Naturals

VARIABLES x, y, ok

vars == <<x, y, ok>>

(* Operators whose bodies contain priming / reference state variables *)
PrimeArg(a)      == a'                 \* prime applied to the parameter
PlusY(a)         == a + y              \* body references state var y
PlusYPrimed(a)   == a + y'             \* body primes state var y directly
XPrimedPlus(a)   == x' + a             \* body primes state var x directly
Sum              == x + y              \* zero-arity operator over state vars
Pair(a, b)       == <<a, b>>

(* Expected next-state values, written directly *)
NextX == (x + 1) % 3
NextY == (y + 2) % 5

(* 1. Priming within operator bodies *)
Check1 ==
    /\ PrimeArg(x) = x'
    /\ PrimeArg(y) = y'
    /\ PrimeArg(7) = 7
    /\ PlusYPrimed(x) = x + y'
    /\ PlusYPrimed(5) = 5 + y'
    /\ XPrimedPlus(y) = x' + y
    /\ XPrimedPlus(y') = x' + y'

(* 2. Priming whole operator applications *)
Check2 ==
    /\ (PlusY(x))' = x' + y'
    /\ (PlusY(3))' = 3 + y'
    /\ Sum' = x' + y'
    /\ (Pair(x, y))' = <<x', y'>>
    /\ (Pair(x, 1))' = <<x', 1>>
    /\ (PlusY(x))' = PlusY(x')
    /\ (PlusY(x))' = PlusYPrimed(x')

(* 3. Priming with LET expressions *)
Check3 ==
    /\ LET u == x IN u' = x'
    /\ LET v == x' IN v = x'
    /\ LET w == x + y IN w' = x' + y'
    /\ LET w == x + y IN w = x + y
    /\ (LET z == x IN z + y)' = x' + y'
    /\ LET g(a) == a + x IN g(y)' = y' + x'
    /\ LET g(a) == a + x IN g(y') = y' + x
    /\ LET h(a) == a' + x IN h(y) = y' + x

(* 4. Parameters vs. state variables: parameter values are not confused
      with the state variables passed in or referenced in the body *)
Check4 ==
    /\ PlusY(y) = y + y
    /\ (PlusY(y))' = y' + y'
    /\ PlusYPrimed(y) = y + y'
    /\ PrimeArg(x + y) = x' + y'
    /\ PrimeArg(Sum) = Sum'
    /\ XPrimedPlus(x) = x' + x

(* Consistency between direct and operator-mediated references *)
Check5 ==
    /\ x' = NextX
    /\ y' = NextY
    /\ Sum' = NextX + NextY
    /\ PrimeArg(x) = NextX

AllChecks == Check1 /\ Check2 /\ Check3 /\ Check4 /\ Check5

TypeOK ==
    /\ x \in 0..2
    /\ y \in 0..4
    /\ ok \in BOOLEAN

Init ==
    /\ x = 0
    /\ y = 0
    /\ ok = TRUE

Next ==
    /\ x' = (x + 1) % 3
    /\ y' = (y + 2) % 5
    /\ ok' = (ok /\ AllChecks)

Spec == Init /\ [][Next]_vars

Inv == TypeOK /\ ok

=============================================================================