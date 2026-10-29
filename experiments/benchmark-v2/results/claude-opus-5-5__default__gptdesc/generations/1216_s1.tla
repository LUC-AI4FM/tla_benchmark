---------------------------- MODULE PrimingTest ----------------------------
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

\* Operator that does not prime its argument
NoPrime(a) == a

\* Operator that primes its argument
PrimeIt(a) == a'

\* Simple non-priming helpers
Inc(a) == (a + 1) % 3
XPlusY == x + y
Same(a, b) == a = b

\* Operator whose body mentions a primed variable directly
XPrimed == x'

\* Operator that compares a primed and an unprimed version of its argument
Changed(a) == a' # a

Init ==
    /\ x = 0
    /\ y = 0

Next ==
    /\ x' = IF x = 0 THEN 1 ELSE IF x = 1 THEN 2 ELSE 0
    /\ y' = IF PrimeIt(x) = 1 THEN Inc(y) ELSE NoPrime(y)
    \* Priming an operator application vs. an operator that primes its argument
    /\ IF NoPrime(x)' = PrimeIt(x) THEN TRUE ELSE FALSE
    \* Priming a LET-bound name vs. a LET-bound primed expression
    /\ LET a == x
           b == x'
       IN  IF a' = b THEN TRUE ELSE FALSE
    \* Priming a LET-bound compound expression
    /\ LET c == XPlusY
       IN  IF c' = x' + y' THEN TRUE ELSE FALSE
    \* Operator whose body contains a primed variable
    /\ IF XPrimed = PrimeIt(x) THEN TRUE ELSE FALSE
    \* Mixing primed and unprimed calls inside IF conditions
    /\ IF PrimeIt(y) = Inc(y) \/ PrimeIt(y) = y THEN TRUE ELSE FALSE
    /\ IF Same(NoPrime(x)', XPrimed) THEN TRUE ELSE FALSE
    /\ IF Changed(x) THEN Same(x', Inc(x)) ELSE TRUE
    \* Nested LET with priming at different levels
    /\ LET d == NoPrime(y)
       IN  LET e == d'
           IN  IF e = PrimeIt(y) THEN TRUE ELSE FALSE

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ x \in 0..2
    /\ y \in 0..2

Inv == TRUE

=============================================================================