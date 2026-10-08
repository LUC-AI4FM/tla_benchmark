MODULE Lock
EXTENDS Naturals, TLC

CONSTANTS P0, P1 \* the two processes {P0,P1}

VARIABLES flag, turn, s, h_turn

(* ------------------------------------------------------------------ *)
(* Helper definitions *)

Other(p) == IF p = P0 THEN P1 ELSE P0

(* ------------------------------------------------------------------ *)
(* Initial state *)

Init ==
    /\ flag   = [p \in {P0,P1} |-> FALSE]
    /\ turn   = P0
    /\ s      = 0
    /\ h_turn = {}              \* history of turns assigned

(* ------------------------------------------------------------------ *)
(* Actions *)

Acquire(p) ==
    LET o == Other(p) IN
    /\ flag[p]   = FALSE
    /\ flag'     = [flag EXCEPT ![p] = TRUE]
    /\ turn'     = o
    /\ h_turn'   = h_turn ∪ {o}
    /\ s'        = 3

Release(p) ==
    /\ flag[p] = TRUE
    /\ flag'   = [flag EXCEPT ![p] = FALSE]
    /\ s'      = 0
    /\ UNCHANGED <<turn, h_turn>>

StutterStep ==
    /\ s > 0
    /\ s'        = s - 1
    /\ UNCHANGED <<flag, turn, h_turn>>

Next == \/ Acquire(P0)
          \/ Acquire(P1)
          \/ Release(P0)
          \/ Release(P1)
          \/ StutterStep

(* ------------------------------------------------------------------ *)
(* Specification *)

Spec ==
    Init
    /\ [][Next]_<<flag,turn,s,h_turn>>
    /\ WF_Exists(Next)

(* ------------------------------------------------------------------ *)
(* Safety invariants *)

MutualExclusion ==
    \A i,j \in {P0,P1} : (i # j) => ~(flag[i] /\ flag[j])

HistoryInvariant ==
    \A v \in h_turn : v = P0 \/ v = P1

Safety == MutualExclusion /\ HistoryInvariant

(* ------------------------------------------------------------------ *)
(* Liveness properties *)

Liveness ==
    \A p \in {P0,P1} :
        ([] (flag[p] => <> s = 0))

============================================================================