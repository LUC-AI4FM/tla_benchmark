---- MODULE GCD ----
EXTENDS Integers

CONSTANTS U_INIT, V_MAX
ASSUME U_INIT = 24 /\ V_MAX = 50

VARIABLES u, v, pc

vars == <<u, v, pc>>

Init ==
    /\ u = U_INIT
    /\ v \in 1..V_MAX
    /\ pc = "Lbl_1"

(* The main loop action, which is taken as long as the pc is "Lbl_1". *)
LoopAction ==
    /\ pc = "Lbl_1"
    /\ IF u # 0
       THEN (* Loop continues: swap if needed, then subtract *)
            LET u_swapped == IF u < v THEN v ELSE u
                v_swapped == IF u < v THEN u ELSE v
            IN  /\ u' = u_swapped - v_swapped
                /\ v' = v_swapped
                /\ pc' = "Lbl_1"
       ELSE (* Loop terminates: u = 0 *)
            /\ pc' = "Done"
            /\ UNCHANGED <<u, v>>

(* Stuttering action for the terminated state. *)
Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ LoopAction
    \/ Done

Spec == Init /\ [][Next]_vars
====