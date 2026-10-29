---- MODULE PrimeTest ----
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

(* Bar constrains the prime of its argument *)
Bar(a) == a' = 2

(* Simple equality checks *)
Foo(a) == a = 2

FooBar(a, b) == a = b

(* LET with a primed expression *)
LetTest == LET z == x' IN z = 2

(* Addition with x *)
Op(a) == a + x

Init ==
    /\ x = 1
    /\ y = 3

Next ==
    \/ /\ x = 1
       /\ x' = 2
       /\ y' = y
       /\ Bar(x)
    \/ /\ IF x = 1
             THEN /\ x' = x + 1
                  /\ PrintT("Test 2 OK: x = 1, x' = 2")
             ELSE /\ x' = 2
                  /\ PrintT("Test 2: x /= 1")
       /\ y' = y
    \/ /\ x' = x
       /\ y' = y

(* Commented-out tests:
    \/ /\ x = 1 /\ x' = 2 /\ y' = y
       /\ Foo(x')                    \* priming a variable within an expression
    \/ /\ x = 1 /\ x' = 2 /\ y' = y
       /\ (x + 1)' = 3               \* priming an entire expression
    \/ /\ x = 1 /\ x' = 2 /\ y' = y
       /\ FooBar(x', 2)
    \/ /\ x = 1 /\ x' = 2 /\ y' = y
       /\ LetTest                    \* priming within LET definitions
    \/ /\ x = 1 /\ x' = 2 /\ y' = y
       /\ Op(1)' = 3                 \* priming operator application with arguments
*)

Inv == TRUE

Spec == Init /\ [][Next]_vars

====