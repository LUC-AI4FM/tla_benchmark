-------------------------------- MODULE GCD --------------------------------
EXTENDS Integers

CONSTANTS InputRange

VARIABLES u, v, pc

vars == <<u, v, pc>>

Init ==
    /\ u = 24
    /\ v \in 1 .. 50
    /\ pc = "Loop"

Loop ==
    /\ pc = "Loop"
    /\ IF u /= 0
       THEN /\ IF u < v
               THEN /\ u' = v
                    /\ v' = u
               ELSE /\ u' = u - v
                    /\ v' = v
            /\ pc' = "Loop"
       ELSE /\ pc' = "Done"
            /\ u' = u
            /\ v' = v

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Loop
    \/ Done

Spec == Init /\ [][Next]_vars

TypeInvariant ==
    /\ u \in Nat
    /\ v \in 1 .. 50
    /\ pc \in {"Loop", "Done"}

Termination ==
    <>(pc = "Done")

GCDCorrectness ==
    pc = "Done" => v = GCD(24, v)

RECURSIVE GCD(_, _)
GCD(a, b) ==
    IF a = 0 THEN b
    ELSE IF b = 0 THEN a
    ELSE IF a < b THEN GCD(a, b - a)
    ELSE GCD(a - b, b)

=============================================================================