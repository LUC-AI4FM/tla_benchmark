------------------------------- MODULE Peterson -------------------------------
(***************************************************************************)
(* Peterson's mutual-exclusion algorithm for two processes, numbered 1    *)
(* and 2.                                                                  *)
(*                                                                         *)
(* Shared variables:                                                       *)
(*   c[p] -- process p's intent to enter the critical section              *)
(*   turn -- whose turn it is                                              *)
(*                                                                         *)
(* Each process cycles through the labels a0, a1, a2, a3, cs, a4:          *)
(*   a0 : non-critical section                                             *)
(*   a1 : c[self] := TRUE                (signal intent)                   *)
(*   a2 : turn := Other(self)            (yield the turn)                  *)
(*   a3 : await ~c[Other(self)] \/ turn = self                             *)
(*   cs : critical section                                                 *)
(*   a4 : c[self] := FALSE               (clear intent)                    *)
(*                                                                         *)
(* The abstract Lock specification is defined inline, so this module      *)
(* parses on its own without a separate Lock module. Its state is         *)
(* obtained through the refinement mapping (pc_translation,              *)
(* lock_translation).                                                     *)
(***************************************************************************)
EXTENDS Naturals, TLAPS

VARIABLES c, turn, pc

vars == << c, turn, pc >>

ProcSet == {1, 2}

Other(p) == IF p = 1 THEN 2 ELSE 1

Labels == {"a0", "a1", "a2", "a3", "cs", "a4"}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Concrete algorithm                                                      *)
(***************************************************************************)
Init == /\ c = [p \in ProcSet |-> FALSE]
        /\ turn \in ProcSet
        /\ pc = [p \in ProcSet |-> "a0"]

a0(self) == /\ pc[self] = "a0"
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << c, turn >>

a1(self) == /\ pc[self] = "a1"
            /\ c' = [c EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED turn

a2(self) == /\ pc[self] = "a2"
            /\ turn' = Other(self)
            /\ pc' = [pc EXCEPT ![self] = "a3"]
            /\ UNCHANGED c

a3(self) == /\ pc[self] = "a3"
            /\ \/ ~ c[Other(self)]
               \/ turn = self
            /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << c, turn >>

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "a4"]
            /\ UNCHANGED << c, turn >>

a4(self) == /\ pc[self] = "a4"
            /\ c' = [c EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a0"]
            /\ UNCHANGED turn

proc(self) == a0(self) \/ a1(self) \/ a2(self) \/ a3(self) \/ cs(self) \/ a4(self)

Next == \E self \in ProcSet : proc(self)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK == /\ c \in [ProcSet -> BOOLEAN]
          /\ turn \in ProcSet
          /\ pc \in [ProcSet -> Labels]

Inv == /\ TypeOK
       /\ \A p \in ProcSet : c[p] <=> pc[p] \in {"a2", "a3", "cs", "a4"}
       /\ \A p \in ProcSet :
             pc[p] \in {"cs", "a4"} =>
                \/ turn = p
                \/ pc[Other(p)] \in {"a0", "a1", "a2"}
       /\ ~ (pc[1] \in {"cs", "a4"} /\ pc[2] \in {"cs", "a4"})

MutualExclusion == ~ (pc[1] = "cs" /\ pc[2] = "cs")

-----------------------------------------------------------------------------
(***************************************************************************)
(* Abstract Lock specification, expressed through the refinement mapping. *)
(* Abstract labels: "l0" idle, "l1" acquiring, "cs" critical section,     *)
(* "l2" releasing. lock = 0 means free, otherwise the holder.             *)
(***************************************************************************)
pc_translation(l) ==
    CASE l = "a0"                 -> "l0"
      [] l \in {"a1", "a2", "a3"} -> "l1"
      [] l = "cs"                 -> "cs"
      [] l = "a4"                 -> "l2"

lock_translation ==
    IF \E p \in ProcSet : pc[p] \in {"cs", "a4"}
    THEN CHOOSE p \in ProcSet : pc[p] \in {"cs", "a4"}
    ELSE 0

lpc  == [p \in ProcSet |-> pc_translation(pc[p])]
lock == lock_translation

lvars == << lpc, lock >>

LInit == /\ lpc = [p \in ProcSet |-> "l0"]
         /\ lock = 0

LRequest(p) == /\ lpc[p] = "l0"
               /\ lpc' = [lpc EXCEPT ![p] = "l1"]
               /\ lock' = lock

LAcquire(p) == /\ lpc[p] = "l1"
               /\ lock = 0
               /\ lpc' = [lpc EXCEPT ![p] = "cs"]
               /\ lock' = p

LExit(p) == /\ lpc[p] = "cs"
            /\ lpc' = [lpc EXCEPT ![p] = "l2"]
            /\ lock' = lock

LRelease(p) == /\ lpc[p] = "l2"
               /\ lpc' = [lpc EXCEPT ![p] = "l0"]
               /\ lock' = 0

LNext == \E p \in ProcSet :
            LRequest(p) \/ LAcquire(p) \/ LExit(p) \/ LRelease(p)

LSpec == LInit /\ [][LNext]_lvars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Theorems                                                                *)
(***************************************************************************)
THEOREM TypeCorrect == Spec => []TypeOK

THEOREM InvInductive == /\ Init => Inv
                        /\ Inv /\ [Next]_vars => Inv'

THEOREM InvAlways == Spec => []Inv

THEOREM Mutex == Spec => []MutualExclusion

THEOREM Refinement == Spec => LSpec
=============================================================================