------------------------------ MODULE LockWithHistory ------------------------------
EXTENDS Naturals, TLC

CONSTANTS PROC \* set of two processes

VARIABLES pc, turn, stutter, turnHist

(* Helper to get the other process *)
OTHER(p) == CHOOSE q ∈ PROC : q # p

Init ==
  /\ pc = [p \in PROC |-> "idle"]
  /\ turn = CHOOSE p \in PROC : TRUE
  /\ stutter = 0
  /\ turnHist = [proc |-> CHOOSE p \in PROC : TRUE,
                  val   |-> CHOOSE q \in PROC : TRUE]

(* Actions *)
Entry(p) ==
  /\ p ∈ PROC
  /\ pc[p] = "idle"
  /\ stutter = 0
  /\ pc' = [pc EXCEPT ![p] = "pre1"]
  /\ stutter' = p
  /\ UNCHANGED <<turn, turnHist>>

PreStep(p) ==
  /\ p ∈ PROC
  /\ pc[p] = "pre1"
  /\ stutter = p
  /\ pc' = [pc EXCEPT ![p] = "pre2"]
  /\ UNCHANGED <<stutter, turn, turnHist>>

SetTurn(p) ==
  /\ p ∈ PROC
  /\ pc[p] = "pre2"
  /\ stutter = p
  /\ turn' = OTHER(p)
  /\ turnHist' = [proc |-> p, val |-> OTHER(p)]
  /\ pc' = [pc EXCEPT ![