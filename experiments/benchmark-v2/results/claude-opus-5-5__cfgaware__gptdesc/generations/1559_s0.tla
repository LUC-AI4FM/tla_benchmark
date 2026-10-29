---------------------------- MODULE LockHS ----------------------------
(***************************************************************************)
(* The Lock specification, extended with auxiliary variables so that it   *)
(* can be shown to refine (and be equivalent to) Peterson's algorithm.    *)
(*                                                                         *)
(*   h_turn : history variable that records the value Peterson's `turn'    *)
(*            variable would be assigned.                                  *)
(*   s      : stuttering variable mimicking the three-step entry protocol  *)
(*            (a1, a2, a3) of Peterson's algorithm.  Steps that only       *)
(*            change s (and h_turn) are stuttering steps of Lock.          *)
(*                                                                         *)
(* The stuttering and history mechanisms of the (modified) Stuttering     *)
(* module are written out inline, and the Peterson specification is       *)
(* instantiated inline via the substitution                               *)
(*   pc <- PPc, flag <- PFlag, turn <- PTurn.                             *)
(***************************************************************************)
EXTENDS Naturals

ProcSet == {0, 1}

Other(p) == 1 - p

VARIABLES pc, h_turn, s

lvars == <<pc>>
vars  == <<pc, h_turn, s>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* The original Lock specification.                                       *)
(***************************************************************************)
LInit == pc = [p \in ProcSet |-> "ncs"]

Enter(p) == /\ pc[p] = "ncs"
            /\ pc[Other(p)] # "cs"
            /\ pc' = [pc EXCEPT ![p] = "cs"]

Exit(p) == /\ pc[p] = "cs"
           /\ pc' = [pc EXCEPT ![p] = "ncs"]

LNext == \E p \in ProcSet : Enter(p) \/ Exit(p)

Spec == LInit /\ [][LNext]_lvars

LockInv == ~(pc[0] = "cs" /\ pc[1] = "cs")

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement mapping to Peterson's variables.                            *)
(***************************************************************************)
PPc   == [p \in ProcSet |-> IF pc[p] = "cs" THEN "cs" ELSE s[p]]
PFlag == [p \in ProcSet |-> pc[p] = "cs" \/ s[p] \in {"a2", "a3"}]
PTurn == h_turn

-----------------------------------------------------------------------------
(***************************************************************************)
(* The specification with history and stuttering variables.               *)
(***************************************************************************)
InitHS == /\ LInit
          /\ h_turn = 0
          /\ s = [p \in ProcSet |-> "a1"]

\* Stuttering step mimicking Peterson's a1 (flag[p] := TRUE)
StepA1(p) == /\ pc[p] = "ncs"
             /\ s[p] = "a1"
             /\ s' = [s EXCEPT ![p] = "a2"]
             /\ UNCHANGED <<pc, h_turn>>

\* Stuttering step mimicking Peterson's a2 (turn := Other(p)); history update
StepA2(p) == /\ pc[p] = "ncs"
             /\ s[p] = "a2"
             /\ s' = [s EXCEPT ![p] = "a3"]
             /\ h_turn' = Other(p)
             /\ UNCHANGED pc

\* The real Enter step, corresponding to Peterson's a3 test succeeding
EnterHS(p) == /\ s[p] = "a3"
              /\ (~PFlag[Other(p)] \/ h_turn = p)
              /\ Enter(p)
              /\ s' = [s EXCEPT ![p] = "a1"]
              /\ UNCHANGED h_turn

ExitHS(p) == /\ Exit(p)
             /\ UNCHANGED <<s, h_turn>>

NextHS == \E p \in ProcSet :
             StepA1(p) \/ StepA2(p) \/ EnterHS(p) \/ ExitHS(p)

SpecHS == InitHS /\ [][NextHS]_vars

TypeOKHS == /\ pc \in [ProcSet -> {"ncs", "cs"}]
            /\ s \in [ProcSet -> {"a1", "a2", "a3"}]
            /\ h_turn \in ProcSet

InvHS == /\ TypeOKHS
         /\ \A p \in ProcSet : pc[p] = "cs" => s[p] = "a1"
         /\ \A p \in ProcSet :
               (PPc[p] = "cs" /\ PPc[Other(p)] \in {"a3", "cs"}) => h_turn = p

-----------------------------------------------------------------------------
(***************************************************************************)
(* Peterson's algorithm, instantiated with                                *)
(*   pc <- PPc, flag <- PFlag, turn <- PTurn                              *)
(***************************************************************************)
PInit == /\ PPc = [p \in ProcSet |-> "a1"]
         /\ PFlag = [p \in ProcSet |-> FALSE]
         /\ PTurn \in ProcSet

Pa1(p) == /\ PPc[p] = "a1"
          /\ PFlag' = [PFlag EXCEPT ![p] = TRUE]
          /\ PPc' = [PPc EXCEPT ![p] = "a2"]
          /\ PTurn' = PTurn

Pa2(p) == /\ PPc[p] = "a2"
          /\ PTurn' = Other(p)
          /\ PPc' = [PPc EXCEPT ![p] = "a3"]
          /\ PFlag' = PFlag

Pa3(p) == /\ PPc[p] = "a3"
          /\ (~PFlag[Other(p)] \/ PTurn = p)
          /\ PPc' = [PPc EXCEPT ![p] = "cs"]
          /\ PFlag' = PFlag
          /\ PTurn' = PTurn

Pcs(p) == /\ PPc[p] = "cs"
          /\ PFlag' = [PFlag EXCEPT ![p] = FALSE]
          /\ PPc' = [PPc EXCEPT ![p] = "a1"]
          /\ PTurn' = PTurn

PNext == \E p \in ProcSet : Pa1(p) \/ Pa2(p) \/ Pa3(p) \/ Pcs(p)

pvars == <<PPc, PFlag, PTurn>>

PSpec == PInit /\ [][PNext]_pvars

=============================================================================