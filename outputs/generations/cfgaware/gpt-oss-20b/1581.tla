------------------------------ MODULE DiningPhilosophers ------------------------------
EXTENDS Naturals

CONSTANT N \* number of philosophers

(* --------------------------------------------------------------------------- *)
(* Variables and auxiliary definitions                                         *)
(* --------------------------------------------------------------------------- *)

VARIABLES pc, sem

State == {"idle","right","left","eat"}

RightFork(i) == i
LeftFork(i)  == (i - 1 + N) % N

(* --------------------------------------------------------------------------- *)
(* Initial state                                                               *)
(* --------------------------------------------------------------------------- *)

Init ==
    /\ pc \in [0..N-1 -> State]
    /\ sem \in [0..N-1 -> BOOLEAN]
    /\ \A i \in 0..N-1 : pc[i] = "idle"
    /\ \A f \in 0..N-1 : sem[f] = TRUE

(* --------------------------------------------------------------------------- *)
(* Actions for each philosopher                                               *)
(* --------------------------------------------------------------------------- *)

PickFirst(i) ==
    /\ i \in 0..N-1
    /\ IF i = 0 THEN
           pc[i] = "idle" /\ sem[LeftFork(i)] = TRUE
       ELSE
           pc[i] = "idle" /\ sem[RightFork(i)] = TRUE
    /\ pc'   = [pc EXCEPT ![i] = IF i=0 THEN "left" ELSE "right"]
    /\ sem'  = [sem EXCEPT 
                ![IF i=0 THEN LeftFork(i) ELSE RightFork(i)] = FALSE]

PickSecond(i) ==
    /\ i \in 0..N-1
    /\ IF i = 0 THEN
           pc[i] = "left" /\ sem[RightFork(i)] = TRUE
       ELSE
           pc[i] = "right" /\ sem[LeftFork(i)] = TRUE
    /\ pc'   = [pc EXCEPT ![i] = "eat"]
    /\ sem'  = [sem EXCEPT 
                ![IF i=0 THEN RightFork(i) ELSE LeftFork(i)] = FALSE]

EatAction(i) ==
    /\ i \in 0..N-1
    /\ pc[i] = "eat"
    /\ pc'   = [pc EXCEPT ![i] = "idle"]
    /\ sem'  = [sem EXCEPT 
                ![RightFork(i)] = TRUE,
                ![LeftFork(i)] = TRUE]

(* --------------------------------------------------------------------------- *)
(* Next-state relation                                                        *)
(* --------------------------------------------------------------------------- *)

Next ==
    \E i \in 0..N-1 :
        CASE pc[i] = "idle" -> PickFirst(i)
             [] ((i = 0 /\ pc[i] = "left") \/ (i > 0 /\ pc[i] = "right")) ->
                 PickSecond(i)
             [] pc[i] = "eat" -> EatAction(i)

(* --------------------------------------------------------------------------- *)
(* Specification                                                              *)
(* --------------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<pc, sem>>

(* --------------------------------------------------------------------------- *)
(* Safety invariant: adjacent philosophers never eat together                  *)
(* --------------------------------------------------------------------------- *)

Invariant ==
    \A i \in 0..N-1 :
        ~(pc[i] = "eat" /\ pc[(i + 1) Mod N] = "eat")

(* --------------------------------------------------------------------------- *)
(* Liveness property: each philosopher eats infinitely often                 *)
(* --------------------------------------------------------------------------- *)

StarvationFree ==
    \A i \in 0..N-1 : []<> (pc[i] = "eat")
============================================================================