---- MODULE Euclid ----
EXTENDS Naturals, TLC

CONSTANT N

VARIABLES pc, u, v, v_ini

(* Control states *)
Start == "Start"
Loop  == "Loop"
Done  == "Done"

Init ==
    /\ pc = Start
    /\ u = 24
    /\ v ∈ 1..N
    /\ v_ini = v

Next ==
    \/ /\ pc = Start
       /\ pc' = Loop
       /\ UNCHANGED <<u, v, v_ini>>
    \/ /\ pc = Loop
       /\ u <> v
       /\ ( IF u > v THEN
                /\ u' = u - v
                /\ v' = v
            ELSE
                /\ u' = u
                /\ v' = v - u )
       /\ v_ini' = v_ini
       /\ pc' = Loop
    \/ /\ pc = Loop
       /\ u = v
       /\ pc' = Done
       /\ UNCHANGED <<u, v, v_ini>>
    \/ /\ pc = Done
       /\ UNCHANGED <<pc, u, v, v_ini>>
    \/ /\ pc' = pc
       /\ u' = u
       /\ v' = v
       /\ v_ini' = v_ini

Inv ==
    /\ 1 <= u
    /\ 1 <= v
    /\ v <= N
    /\ v_ini ∈ 1..N

Spec == Init /\ [][Next]_<<pc,u,v,v_ini>> /\ WF_∈{Next} /\ Inv

Termination == <> (pc = Done)

THEOREM TerminationIsTrue ==
    Spec => Termination

====