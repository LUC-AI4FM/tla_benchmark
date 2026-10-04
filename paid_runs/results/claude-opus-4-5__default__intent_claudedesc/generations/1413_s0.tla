---------------------------- MODULE TrivialTautology ----------------------------
(******************************************************************************)
(* A minimal, trivial system used to verify a temporal logic tautology with   *)
(* the TLA+ proof system (TLAPS).                                             *)
(*                                                                            *)
(* The system has a single variable that never changes, initialized to zero,  *)
(* with a stuttering-only next-state relation.                                *)
(*                                                                            *)
(* The property to verify is the temporal tautology:                          *)
(*   <>TRUE => <>[]TRUE                                                       *)
(*                                                                            *)
(* This serves as a regression test or demonstration that TLAPS can discharge *)
(* simple propositional temporal logic obligations automatically.             *)
(******************************************************************************)

EXTENDS Naturals, TLAPS

VARIABLES x

(******************************************************************************)
(* Type invariant: x is always a natural number                               *)
(******************************************************************************)
TypeOK == x \in Nat

(******************************************************************************)
(* Initial state: x is initialized to zero                                    *)
(******************************************************************************)
Init == x = 0

(******************************************************************************)
(* Next-state relation: stuttering only (x never changes)                     *)
(******************************************************************************)
Next == UNCHANGED x

(******************************************************************************)
(* The specification with stuttering                                          *)
(******************************************************************************)
Spec == Init /\ [][Next]_x

(******************************************************************************)
(* The temporal tautology we want to verify:                                  *)
(* If eventually TRUE holds, then eventually TRUE holds forever.              *)
(******************************************************************************)
Tautology == <>TRUE => <>[]TRUE

(******************************************************************************)
(* Alternative formulation: since TRUE is always true, <>TRUE is TRUE         *)
(* and []TRUE is TRUE, so <>[]TRUE is also TRUE.                              *)
(******************************************************************************)
SimpleTautology == <>[]TRUE

(******************************************************************************)
(* Safety invariant: x remains zero (implied by stuttering-only behavior)     *)
(******************************************************************************)
Invariant == x = 0

(******************************************************************************)
(* The complete specification implies the tautology                           *)
(******************************************************************************)
THEOREM SpecImpliesTautology == Spec => Tautology
<1>1. TRUE
  OBVIOUS
<1>2. []TRUE
  BY <1>1
<1>3. <>[]TRUE
  BY <1>2
<1>4. <>TRUE => <>[]TRUE
  BY <1>3
<1>5. QED
  BY <1>4

(******************************************************************************)
(* Direct proof that the tautology holds (independent of Spec)                *)
(******************************************************************************)
THEOREM TautologyHolds == Tautology
<1>1. []TRUE
  OBVIOUS
<1>2. <>[]TRUE
  BY <1>1
<1>3. QED
  BY <1>2

(******************************************************************************)
(* Proof that SimpleTautology holds                                           *)
(******************************************************************************)
THEOREM SimpleTautologyHolds == SimpleTautology
<1>1. []TRUE
  OBVIOUS
<1>2. QED
  BY <1>1

(******************************************************************************)
(* Proof that the invariant is preserved                                      *)
(******************************************************************************)
THEOREM InvariantPreserved == Spec => []Invariant
<1>1. Init => Invariant
  BY DEF Init, Invariant
<1>2. Invariant /\ [Next]_x => Invariant'
  BY DEF Invariant, Next
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

(******************************************************************************)
(* Proof that TypeOK is preserved                                             *)
(******************************************************************************)
THEOREM TypeOKPreserved == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_x => TypeOK'
  BY DEF TypeOK, Next
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

=============================================================================