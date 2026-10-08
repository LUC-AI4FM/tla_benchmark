------------------------------- MODULE TerminationDetection ------------------------------

CONSTANTS N

VARIABLES active, terminationDetected

ASSUME N \in Nat /\ N > 0

(*--algorithm TerminationDetection
variables 
    active = [i \in 1..N -> BOOLEAN], 
    terminationDetected = FALSE;

fair process (node \in 1..N) \in
1: while TRUE do
2:     either
3:         if active[node] then
4:             await \E j \in 1..N : j # node /\ active[j]
5:             with (j \in 1..N) \ {node} do
6:                 active[j] := FALSE;
7:             endwith;
8:         else
9:             skip;
10:        endif;
11:     or
12:         if active[node] then
13:             await \E j \in 1..N : j # node /\ ~active[j]
14:             with (j \in 1..N) \ {node} do
15:                 active[j] := TRUE;
16:             endwith;
17:         else
18:             skip;
19:        endif;
20:     or
21:         if ~active[node] then
22:             active[node] := FALSE;
23:         else
24:             skip;
25:        endif;
26:    endeither;
27: od;

fair process Detection \in
28: while TRUE do
29:     await \A i \in 1..N : ~active[i];
30:     terminationDetected := TRUE;
31:     await FALSE;
32: od;

end algorithm;)

Spec == /\ Init
        /\ [][Next]_<<active, terminationDetected>>
        /\ WF_fair(Detection)_<<active, terminationDetected>>

Init == /\ active \in [1..N -> BOOLEAN]
        /\ (terminationDetected = TRUE) => (\A i \in 1..N : ~active[i])

Next ==
    \/ \E node \in 1..N :
        (   \/ (active[node] /\ \E j \in 1..N : j # node /\ active[j])
            \/ (active[node] /\ \E j \in 1..N : j # node /\ ~active[j])
            \/ (~active[node]) )
    \/ (\A i \in 1..N : ~active[i]) => terminationDetected' = TRUE

WF_fair(Detection) == WF(Detection, <<active, terminationDetected>>)

(* Correctness properties *)
TerminationNeverFalse ==
    [](terminationDetected => [](\A i \in 1..N : ~active[i]))

StableTermination ==
    [](terminationDetected => []terminationDetected)

Liveness ==
    <>(\A i \in 1..N : ~active[i]) => <>terminationDetected

THEOREM Spec => []<>(terminationDetected)
=============================================================================