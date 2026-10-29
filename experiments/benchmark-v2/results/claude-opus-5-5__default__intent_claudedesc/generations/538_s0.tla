---- MODULE SquareByOddSums ----
EXTENDS Naturals

CONSTANT Input

ASSUME InputAssumption == Input \subseteq Nat

VARIABLES n, i, x, odd, done

vars == <<n, i, x, odd, done>>

TypeOK ==
    /\ n \in Input
    /\ i \in Nat
    /\ x \in Nat
    /\ odd \in Nat
    /\ done \in BOOLEAN

Init ==
    /\ n \in Input
    /\ i = 0
    /\ x = 0
    /\ odd = 1
    /\ done = FALSE

Step ==
    /\ ~done
    /\ i < n
    /\ x' = x + odd
    /\ odd' = odd + 2
    /\ i' = i + 1
    /\ UNCHANGED <<n, done>>

Finish ==
    /\ ~done
    /\ i = n
    /\ done' = TRUE
    /\ UNCHANGED <<n, i, x, odd>>

Terminated ==
    /\ done
    /\ UNCHANGED vars

Next == Step \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ Finish)

LoopInvariant ==
    /\ i <= n
    /\ x = i * i
    /\ odd = 2 * i + 1

PartialCorrectness == done => (x = n * n)

Inv == TypeOK /\ LoopInvariant /\ PartialCorrectness

Termination == <>done

ResultCorrect == <>(done /\ x = n * n)

====