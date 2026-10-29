------------------------------ MODULE UnchangedTest ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES x, y

vars == <<x, y>>

N == 3

Init ==
    /\ x = [i \in 1..N |-> i]
    /\ y = 0

\* Helper: check an assertion and print a success message
Check(cond, name) ==
    /\ Assert(cond, <<"Test failed:", name>>)
    /\ PrintT(<<"Test passed:", name>>)

-----------------------------------------------------------------------------
\* Part 1: the whole state remains unchanged; UNCHANGED of derived
\* expressions must evaluate to TRUE.
-----------------------------------------------------------------------------
AllUnchanged ==
    /\ x' = x
    /\ y' = y
    \* 1. array element with primed equality
    /\ Check(x'[1] = x[1], "1: primed equality on array element")
    \* 2. array element with UNCHANGED
    /\ Check(UNCHANGED x[1], "2: UNCHANGED on array element")
    \* 3. record built from array values
    /\ Check(UNCHANGED [a |-> x[1], b |-> x[2]], "3: UNCHANGED on record")
    \* 4. existential quantification
    /\ Check(UNCHANGED (\E i \in DOMAIN x : x[i] = 2), "4: UNCHANGED on \\E")
    \* 5. universal quantification
    /\ Check(UNCHANGED (\A i \in DOMAIN x : x[i] > 0), "5: UNCHANGED on \\A")
    \* 6. CHOOSE
    /\ Check(UNCHANGED (CHOOSE i \in DOMAIN x : x[i] = 2), "6: UNCHANGED on CHOOSE")
    \* 7. set comprehension mapping over indices
    /\ Check(UNCHANGED {x[i] : i \in DOMAIN x}, "7: UNCHANGED on set map")
    \* 8. set comprehension with filter
    /\ Check(UNCHANGED {i \in DOMAIN x : x[i] > 1}, "8: UNCHANGED on set filter")
    \* 9. domain of the array
    /\ Check(UNCHANGED DOMAIN x, "9: UNCHANGED on DOMAIN")
    \* 10. set containing the entire array
    /\ Check(UNCHANGED {x}, "10: UNCHANGED on set containing array")
    \* 11. set mixing constants and a variable
    /\ Check(UNCHANGED {0, 1, y}, "11: UNCHANGED on mixed set")
    /\ Check(UNCHANGED <<x, y>>, "12: UNCHANGED on full tuple")

-----------------------------------------------------------------------------
\* Part 2: part of the state changes (x[1] and x[3] are swapped, y toggles),
\* yet UNCHANGED applied to expressions whose VALUE stays the same must
\* evaluate to TRUE.
-----------------------------------------------------------------------------
PartlyChanged ==
    /\ x' = [x EXCEPT ![1] = x[3], ![3] = x[1]]
    /\ y' = (y + 1) % 2
    \* 1. untouched element via primed equality
    /\ Check(x'[2] = x[2], "P1: primed equality on untouched element")
    \* 2. untouched element via UNCHANGED
    /\ Check(UNCHANGED x[2], "P2: UNCHANGED on untouched element")
    \* 3. record built from untouched values
    /\ Check(UNCHANGED [m |-> x[2], s |-> x[1] + x[3]], "P3: UNCHANGED on record")
    \* 4. existential quantification
    /\ Check(UNCHANGED (\E i \in DOMAIN x : x[i] = 1), "P4: UNCHANGED on \\E")
    \* 5. universal quantification
    /\ Check(UNCHANGED (\A i \in DOMAIN x : x[i] \in 1..N), "P5: UNCHANGED on \\A")
    \* 6. CHOOSE selecting the (unmoved) middle value
    /\ Check(UNCHANGED (CHOOSE i \in DOMAIN x : x[i] = 2), "P6: UNCHANGED on CHOOSE")
    \* 7. set comprehension mapping over indices (permutation invariant)
    /\ Check(UNCHANGED {x[i] : i \in DOMAIN x}, "P7: UNCHANGED on set map")
    \* 8. set comprehension with filter on values
    /\ Check(UNCHANGED {x[i] : i \in {j \in DOMAIN x : x[j] >= 2}},
             "P8: UNCHANGED on filtered set")
    \* 9. domain of the array
    /\ Check(UNCHANGED DOMAIN x, "P9: UNCHANGED on DOMAIN")
    \* 10. set of all arrays reachable by swapping ends: {x, swapped x}
    /\ Check(UNCHANGED {x, [x EXCEPT ![1] = x[3], ![3] = x[1]]},
             "P10: UNCHANGED on set containing array")
    \* 11. set mixing constants and a changing value
    /\ Check(UNCHANGED {0, 1, y}, "P11: UNCHANGED on mixed set")
    \* sanity: the state really did change
    /\ Check(~ UNCHANGED x, "P12: x actually changed")
    /\ Check(~ UNCHANGED y, "P13: y actually changed")

Next ==
    \/ AllUnchanged
    \/ PartlyChanged

Spec == Init /\ [][Next]_vars

Inv ==
    /\ DOMAIN x = 1..N
    /\ \A i \in 1..N : x[i] \in 1..N
    /\ y \in {0, 1}

=============================================================================