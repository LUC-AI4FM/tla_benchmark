------------------------------- MODULE TerminationDetection ------------------------------

CONSTANTS N

VARIABLES active, pending, terminationDetected

ASSUME N \in Nat /\ N > 0

(*--algorithm TerminationDetection
variables 
    active = [i \in 1..N -> BOOLEAN],
    pending = [i \in 1..N -> 0],
    terminationDetected = FALSE;

fair process (node \in 1..N) \in
1: while TRUE do
2:     either
3:         /\ active[node]
4:         \/ /\ active[node] := FALSE;
5:            \/ /\ IF (\A i \in 1..N : ~active[i] /\ pending[i] = 0)
6:                 THEN terminationDetected := TRUE;
7:              FI
8:     or
9:         /\ active[node]
10:        \/ /\ dest \in 1..N;
11:           /\ pending[dest] := pending[dest] + 1;
12:    or
13:        /\ pending[node] > 0
14:        \/ /\ pending[node] := pending[node] - 1;
15:           /\ active[node] := TRUE;
16:    or
17:        /\ IF (\A i \in 1..N : ~active[i] /\ pending[i] = 0)
18:             THEN terminationDetected := TRUE;
19:          FI
20:    end either;
21: od;

end process;
end algorithm;*)

TypeOK == 
    /\ active \in [1..N -> BOOLEAN]
    /\ pending \in [1..N -> 0..3]
    /\ terminationDetected \in BOOLEAN

Init ==
    /\ TypeOK
    /\ (\A i \in 1..N : pending[i] = 0)
    /\ (terminationDetected <-> (\A i \in 1..N : ~active[i]))

Terminate(node) ==
    /\ active[node]
    /\ active' = [active EXCEPT ![node] = FALSE]
    /\ pending' = pending
    /\ terminationDetected' =
        IF (\A i \in 1..N : ~active[i] /\ pending[i] = 0)
        THEN TRUE
        ELSE terminationDetected

SendMsg(node, dest) ==
    /\ active[node]
    /\ pending'[dest] = pending[dest] + 1
    /\ active' = active
    /\ terminationDetected' = terminationDetected
    /\ pending'' = [pending' EXCEPT ![dest] = pending'[dest]]

RcvMsg(node) ==
    /\ pending[node] > 0
    /\ pending'[node] = pending[node] - 1
    /\ active'[node] = TRUE
    /\ terminationDetected' = terminationDetected
    /\ pending'' = [pending' EXCEPT ![node] = pending'[node]]

DetectTermination ==
    /\ IF (\A i \in 1..N : ~active[i] /\ pending[i] = 0)
         THEN terminationDetected' := TRUE
         ELSE terminationDetected'
    /\ active' = active
    /\ pending' = pending

Next ==
    \/ (\/ node \in 1..N : Terminate(node))
     \/ (\/ node, dest \in 1..N : SendMsg(node, dest))
     \/ (\/ node \in 1..N : RcvMsg(node))
     \/ DetectTermination

Spec == Init /\ [][Next]_<<active, pending, terminationDetected>> /\ WF_next(DetectTermination)

Safe ==
    terminationDetected -> (\A i \in 1..N : ~active[i] /\ pending[i] = 0)

Live ==
    <>(terminationDetected) /\ [](terminationDetected -> []terminationDetected)

Quiescence ==
    [](terminationDetected -> (/\ active' = active
                               /\ pending' = pending))

IndInv == TypeOK /\ Safe

WF_next(action) == <<action>>_<<active, pending, terminationDetected>>

WF_Terminate(node) == WF_next(Terminate(node))
WF_SendMsg(node, dest) == WF_next(SendMsg(node, dest))
WF_RcvMsg(node) == WF_next(RcvMsg(node))

=============================================================================