---- MODULE MCLeastCircularSubstring ----
EXTENDS Sequences

N == INSTANCE Naturals

CONSTANTS CharSetSize, MaxStringLength

VARIABLES input, best, i, pc

vars == <<input, best, i, pc>>

Add(a, b) == N!+(a, b)
Sub(a, b) == N!-(a, b)
Lt(a, b)  == N!<(a, b)
Leq(a, b) == N!<=(a, b)
Mod(a, b) == N!%(a, b)
Range(a, b) == N!..(a, b)

MCCharacterSet == Range(0, Sub(CharSetSize, 1))

CharacterSet == MCCharacterSet

Nat == Range(0, MaxStringLength)

Strings == UNION { [Range(1, n) -> CharacterSet] : n \in Nat }

Rotation(s, r) ==
    [k \in Range(1, Len(s)) |-> s[Add(Mod(Add(Sub(k, 1), r), Len(s)), 1)]]

LexLess(a, b) ==
    \E k \in Range(1, Len(a)) :
        /\ \A j \in Range(1, Sub(k, 1)) : a[j] = b[j]
        /\ Lt(a[k], b[k])

LexLeq(a, b) == (a = b) \/ LexLess(a, b)

Init ==
    /\ input \in Strings
    /\ best = 0
    /\ i = 1
    /\ pc = "loop"

Step ==
    /\ pc = "loop"
    /\ Lt(i, Len(input))
    /\ best' = IF LexLess(Rotation(input, i), Rotation(input, best))
                 THEN i ELSE best
    /\ i' = Add(i, 1)
    /\ UNCHANGED <<input, pc>>

Finish ==
    /\ pc = "loop"
    /\ ~Lt(i, Len(input))
    /\ pc' = "Done"
    /\ UNCHANGED <<input, best, i>>

Terminated ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Step \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeInvariant ==
    /\ input \in Strings
    /\ best \in Nat
    /\ i \in Range(0, Add(MaxStringLength, 1))
    /\ pc \in {"loop", "Done"}

Correctness ==
    pc = "Done" =>
        \A r \in Range(0, Sub(Len(input), 1)) :
            LexLeq(Rotation(input, best), Rotation(input, r))

====