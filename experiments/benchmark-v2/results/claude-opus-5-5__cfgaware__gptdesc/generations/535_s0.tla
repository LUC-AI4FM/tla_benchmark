---------------------------- MODULE MCSession5 ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS minValue, Tuples

VARIABLES pending, maxSeen, done

vars == <<pending, maxSeen, done>>

ConstMinValue == -99999

ConstTuples == { <<1, 2, 3>> }

Range(t) == { t[i] : i \in DOMAIN t }

MaxOf(S) == CHOOSE x \in S : \A y \in S : y <= x

Max2(a, b) == IF a >= b THEN a ELSE b

Init ==
    /\ pending = Tuples
    /\ maxSeen = minValue
    /\ done = FALSE

Process ==
    /\ pending # {}
    /\ \E t \in pending :
        /\ pending' = pending \ {t}
        /\ maxSeen' = IF Range(t) = {} THEN maxSeen
                      ELSE Max2(maxSeen, MaxOf(Range(t)))
    /\ UNCHANGED done

Finish ==
    /\ pending = {}
    /\ ~done
    /\ done' = TRUE
    /\ UNCHANGED <<pending, maxSeen>>

Terminated ==
    /\ done
    /\ UNCHANGED vars

Next == Process \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Process) /\ WF_vars(Finish)

Termination == <>(done)

=============================================================================