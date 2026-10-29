---------------------------- MODULE PrimingTest ----------------------------
(***************************************************************************)
(* Test module exploring how priming interacts with operator application, *)
(* LET bindings and IF-THEN-ELSE expressions in TLA+.  It models no real  *)
(* system.                                                                 *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLES x, y

vars == <<x, y>>

(***************************************************************************)
(* Operators that prime their argument and operators that do not.          *)
(***************************************************************************)
Prime(a)    == a'          \* primes its argument
Id(a)       == a           \* does not prime its argument
XPrimed     == x'          \* refers directly to primed variable x
YPrimed     == y'          \* refers directly to primed variable y
XUnprimed   == x           \* refers directly to unprimed variable x
YUnprimed   == y           \* refers directly to unprimed variable y
Succ(a)     == (a + 1) % N
PrimeSucc(a) == (a' + 1) % N
SuccPrime(a) == Succ(a)'   \* the whole application is primed

TypeOK == /\ x \in 0..(N-1)
          /\ y \in 0..(N-1)

Init == /\ x = 0
        /\ y = 0

Next ==
    /\ x' = IF x < N - 1 THEN x + 1 ELSE 0
    \* y' is defined using the primed operator applied to x
    /\ y' = IF Prime(x) = Succ(x)
               THEN Succ(Id(y))
               ELSE 0
    \* Priming an unprimed operator application is the same as applying
    \* the priming operator.
    /\ IF Id(x)' = Prime(x) THEN TRUE ELSE FALSE
    \* Operators referring directly to variables
    /\ IF XPrimed = Id(x)' THEN TRUE ELSE FALSE
    /\ IF XUnprimed' = XPrimed THEN TRUE ELSE FALSE
    /\ IF YUnprimed' = YPrimed THEN TRUE ELSE FALSE
    \* LET bindings: one binding primes, one does not
    /\ LET a == Prime(x)
           b == Id(x)
           c == b'
       IN  IF a = c
              THEN a = XPrimed
              ELSE FALSE
    \* LET binding that captures the unprimed state value
    /\ LET old == Id(x)
           new == Prime(x)
       IN  IF old = N - 1
              THEN new = 0
              ELSE new = old + 1
    \* Priming a compound expression vs. priming its subterms
    /\ IF SuccPrime(x) = Succ(Prime(x))
          THEN SuccPrime(x) = PrimeSucc(x)
          ELSE FALSE
    \* Nested IF with mixed primed and unprimed operator calls
    /\ IF Id(y) = 0
          THEN IF Prime(y) = Succ(0) THEN TRUE ELSE FALSE
          ELSE IF Prime(y) = Succ(Id(y)) \/ Prime(y) = 0
                  THEN TRUE
                  ELSE FALSE

Spec == Init /\ [][Next]_vars

Inv == TRUE

THEOREM Spec => []Inv
THEOREM Spec => []TypeOK
=============================================================================