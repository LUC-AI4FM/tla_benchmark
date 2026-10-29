------------------------------- MODULE LockHS -------------------------------
(***************************************************************************)
(* A lock specification augmented with auxiliary variables so that it can *)
(* be related to Peterson's mutual exclusion algorithm.                    *)
(*                                                                         *)
(*  - h_turn is a history variable. It records the value that Peterson's  *)
(*    algorithm would assign to its variable turn.                          *)
(*  - s is a stuttering variable, in the style of the Stuttering module    *)
(*    with some modifications. It adds a stuttering step to the lock's     *)
(*    request action so that the lock's entry protocol mimics the          *)
(*    three-step entry protocol of Peterson's algorithm: set the flag,     *)
(*    set turn, then await and enter.                                       *)
(*                                                                         *)
(* The Peterson specification is given as a submodule. It is instantiated *)
(* under a refinement mapping that relates the two systems.                *)
(***************************************************************************)
EXTENDS Naturals

  --------------------------- MODULE Peterson ------------------------------
  (*************************************************************************)
  (* Peterson's algorithm for two processes 0 and 1.                       *)
  (*   a1: c[self] := TRUE                                                 *)
  (*   a2: turn := Other(self)                                              *)
  (*   a3: await ~c[Other(self)] \/ turn = self                             *)
  (*   cs: critical section, then c[self] := FALSE                          *)
  (*************************************************************************)
  VARIABLES pc, c, turn

  pvars == <<pc, c, turn>>

  PProcs == {0, 1}

  POther(p) == 1 - p

  PTypeOK ==
    /\ pc \in [PProcs -> {"a1", "a2", "a3", "cs"}]
    /\ c \in [PProcs -> BOOLEAN]
    /\ turn \in PProcs

  PInit ==
    /\ pc = [p \in PProcs |-> "a1"]
    /\ c = [p \in PProcs |-> FALSE]
    /\ turn \in PProcs

  A1(p) ==
    /\ pc[p] = "a1"
    /\ c' = [c EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = "a2"]
    /\ UNCHANGED turn

  A2(p) ==
    /\ pc[p] = "a2"
    /\ turn' = POther(p)
    /\ pc' = [pc EXCEPT ![p] = "a3"]
    /\ UNCHANGED c

  A3(p) ==
    /\ pc[p] = "a3"
    /\ (~c[POther(p)]) \/ (turn = p)
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED <<c, turn>>

  CS(p) ==
    /\ pc[p] = "cs"
    /\ c' = [c EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "a1"]
    /\ UNCHANGED turn

  PProc(p) == A1(p) \/ A2(p) \/ A3(p) \/ CS(p)

  PNext == \E p \in PProcs : PProc(p)

  PSpec == /\ PInit
           /\ [][PNext]_pvars
           /\ \A p \in PProcs : WF_pvars(PProc(p))

  PMutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")

  PStarvationFree == \A p \in PProcs : (pc[p] = "a2") ~> (pc[p] = "cs")
  ==========================================================================