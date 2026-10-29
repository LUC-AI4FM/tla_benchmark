-------------------------- MODULE HourClock2_typedefs --------------------------
(***************************************************************************)
(* Type annotations for the HourClock2 specification so that it can be     *)
(* checked with Apalache while keeping the original specification free of  *)
(* tool-specific syntax.                                                   *)
(*                                                                         *)
(* The original module does:   INSTANCE HourClock2                         *)
(* To keep this module self-contained for SANY, the definitions of         *)
(* HourClock2 are reproduced below.                                        *)
(*                                                                         *)
(* HourClock2 computes the next hour with modular arithmetic,              *)
(* (hr % 12) + 1, rather than with an IF/THEN/ELSE. The temporal           *)
(* specifications HC (from HourClock) and HC2 are claimed equivalent:      *)
(*     THEOREM HC <=> HC2                                                  *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES
    \* @type: Int;
    hr

vars == << hr >>

(***************************************************************************)
(* Definitions from HourClock2                                             *)
(***************************************************************************)
HCini == hr \in (1 .. 12)

HCnxt2 == hr' = (hr % 12) + 1

HC2 == HCini /\ [][HCnxt2]_hr

(***************************************************************************)
(* Standard names                                                          *)
(***************************************************************************)
Init == HCini

Next == HCnxt2

Spec == HC2

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK == hr \in Nat

\* The invariant checked by the model-checking configuration:
\* the hour always stays within 1 .. 12.
Inv == HCini

THEOREM HC2 => []HCini
=============================================================================