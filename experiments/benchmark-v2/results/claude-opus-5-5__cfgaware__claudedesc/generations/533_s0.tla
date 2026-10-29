---------------------------- MODULE Session4 ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS minValue, Tuples

ASSUME minValue \in Int

VARIABLES processed, maxSeen, current

vars == <<processed, maxSeen, current>>

ElemsOf(t) == { t[i] : i \in DOMAIN t }

MaxOf(S, base) == IF S = {} THEN base
                  ELSE CHOOSE m \in S \cup {base} :
                         \A x \in S \cup {base} : x <= m

TypeOK ==
    /\ processed \subseteq Tuples
    /\ maxSeen \in Int
    /\ current \in Tuples \cup {<<>>}

Init ==
    /\ processed = {}
    /\ maxSeen = minValue
    /\ current = <<>>

Process(t) ==
    /\ t \in Tuples \ processed
    /\ processed' = processed \cup {t}
    /\ current' = t
    /\ maxSeen' = MaxOf(ElemsOf(t), maxSeen)

Done ==
    /\ processed = Tuples
    /\ UNCHANGED vars

Next == (\E t \in Tuples : Process(t)) \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(\E t \in Tuples : Process(t))

MaxIsBounded == maxSeen >= minValue

MaxIsCorrect ==
    \A t \in processed : \A x \in ElemsOf(t) : x <= maxSeen

EventuallyAllProcessed == <>(processed = Tuples)

-----------------------------------------------------------------------------
\* Model-checking configuration bindings

ConstMinValue == -99999

ConstTuples == UNION { [1..l -> (l+1)..(2*l)] : l \in 0..5 }

=============================================================================