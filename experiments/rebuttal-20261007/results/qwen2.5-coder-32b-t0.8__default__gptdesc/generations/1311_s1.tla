------------------------------- MODULE GCDLoop -------------------------------
EXTENDS Integers, TLC

CONSTANTS MaxV

VARIABLES u, v, pc

(*--algorithm GCDLoop
variables u = 24, v \in 1..MaxV, pc = "start";
begin
Init:
    if
        \/ pc = "start" -> begin u := 24; v := CHOOSE x \in 1..MaxV : TRUE; pc := "loop" end
    else
        skip;
Loop:
    either
        if
            \/ pc = "loop" /\ u < v -> begin temp := u; u := v; v := temp; pc := "loop" end
            \/ pc = "loop" /\ u >= v -> begin u := u - v; pc := "loop" end
    else skip;
Done:
    if
        \/ pc = "done" -> pc := "done"
    else
        skip;
end algorithm *)

Init == (u = 24) /\ (v \in 1..MaxV) /\ (pc = "start")

Next ==
    \/  /\ (pc = "start")
        /\ (u' = 24)
        /\ (v' \in 1..MaxV)
        /\ (pc' = "loop")
    \/  /\ (pc = "loop") /\ (u < v)
        /\ (u' = v)
        /\ (v' = u)
        /\ (pc' = "loop")
    \/  /\ (pc = "loop") /\ (u >= v)
        /\ (u' = u - v)
        /\ (v' = v)
        /\ (pc' = "loop" \/ pc' = "done")
    \/  /\ (pc = "done")
        /\ (u' = u)
        /\ (v' = v)
        /\ (pc' = "done")

Spec ==
    /\ Init
    /\ [][Next]_<<u, v, pc>>
    /\ WF_next(_<<u, v, pc>>, Done)

Done == (pc = "done") /\ (u = 0) /\ (v > 0)
=============================================================================