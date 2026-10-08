MODULE FastMutex
EXTENDS Naturals, Sequences

CONSTANT N

VARIABLES x, y, b, S, inCS

ProcessSet == 1 .. N

vars == <<x,y,b,S,inCS>>

Init ==
    /\ x = 0
    /\ y = 0
    /\ b \in [ProcessSet -> BOOLEAN]
    /\ S \subseteq ProcessSet
    /\ inCS \in [ProcessSet -> BOOLEAN]
    /\ (\A i ∈ ProcessSet : b[i] = FALSE)
    /\ S = {}
    /\ (\A i ∈ ProcessSet : inCS[i] = FALSE)

TryEnter(i) ==
    /\ i ∈ ProcessSet
    /\ b[i] = FALSE
    /\ x' = i
    /\ y' = y
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ S' = S \cup {i}
    /\ UNCHANGED <<inCS>>

EnterCS(i) ==
    /\ i ∈ ProcessSet
    /\ x = i
    /\ y = 0
    /\ b[i] = TRUE
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ S' = S \ {i}
    /\ UNCHANGED <<x,y>>

ExitCS(i) ==
    /\ i ∈ ProcessSet
    /\ inCS[i] = TRUE
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ S' = S
    /\ UNCHANGED <<x,y>>

Next ==
    \E i ∈ ProcessSet : (TryEnter(i) \/ EnterCS(i) \/ ExitCS(i))

MutualExcl ==
    \A i, j ∈ ProcessSet :
        (i # j) => ~(inCS[i] /\ inCS[j])

Liveliness ==
    [] <> (\E i ∈ ProcessSet : inCS[i])

Spec == Init /\ [][Next]_vars /\ WF(Next)

END MODULE