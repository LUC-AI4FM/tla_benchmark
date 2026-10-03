---- MODULE Euclid ----
EXTENDS Integers, TLC

CONSTANT N

VARIABLES pc, u, v, v_ini

vars == <<pc, u, v, v_ini>>

\* PlusCal algorithm translated to TLA+
\* --algorithm Euclid
\* {
\*   variables u = 24, v \in 1..N, v_ini;
\*   begin
\*     Lbl_1:
\*       v_ini := v;
\*     Lbl_2:
\*       while (u /= v) {
\*         if (u > v) {
\*           u := u - v;
\*         } else {
\*           v := v - u;
\*         }
\*       };
\* }
\* --algorithm

\* BEGIN TRANSLATION

Init == (* Initial state predicate *)
    /\ u = 24
    /\ v \in 1..N
    /\ pc = "Lbl_1"

Lbl_1 == (* v_ini := v *)
    /\ pc = "Lbl_1"
    /\ v_ini' = v
    /\ pc' = "Lbl_2"
    /\ UNCHANGED <<u, v>>

Lbl_2 == (* while (u /= v) ... *)
    /\ pc = "Lbl_2"
    /\ IF u = v
       THEN /\ pc' = "Done"
            /\ UNCHANGED <<u, v, v_ini>>
       ELSE /\ IF u > v
               THEN /\ u' = u - v
                    /\ v' = v
               ELSE /\ v' = v - u
                    /\ u' = u
            /\ pc' = "Lbl_2"
            /\ UNCHANGED <<v_ini>>

Next == Lbl_1 \/ Lbl_2

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

\* END TRANSLATION
=============================================================================