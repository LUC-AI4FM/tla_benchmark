---------------------------- MODULE stages ----------------------------
EXTENDS Naturals

(***************************************************************************)
(* Nested abstract ("clean") model of PCR, with no stage ordering.         *)
(* The staged model below refines it.                                      *)
(***************************************************************************)
---------------------------- MODULE clean -----------------------------
CONSTANTS DNA, PRIMER

VARIABLES tee, primer, dna, template, hybrid

cvars == <<tee, primer, dna, template, hybrid>>

cNatMin(i, j) == IF i < j THEN i ELSE j

CTypeOK ==
    /\ tee \in {"Hot", "Warm", "TooHot"}
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat

CInit ==
    /\ tee = "Hot"
    /\ primer = PRIMER
    /\ dna = DNA
    /\ template = 0
    /\ hybrid = 0

CHeat ==
    /\ tee \in {"Hot", "Warm"}
    /\ tee' = "TooHot"
    /\ primer' = primer + hybrid
    /\ dna' = 0
    /\ template' = template + hybrid + 2 * dna
    /\ hybrid' = 0

CCool ==
    /\ tee = "TooHot"
    /\ tee' = "Hot"
    /\ UNCHANGED <<primer, dna, template, hybrid>>

CAnneal ==
    /\ tee = "Hot"
    /\ tee' = "Warm"
    /\ UNCHANGED dna
    /\ \E k \in 1..cNatMin(primer, template) :
          /\ primer' = primer - k
          /\ template' = template - k
          /\ hybrid' = hybrid + k

CExtend ==
    /\ tee = "Warm"
    /\ tee' = "Hot"
    /\ UNCHANGED <<primer, template>>
    /\ dna' = dna + hybrid
    /\ hybrid' = 0

CNext == CHeat \/ CCool \/ CAnneal \/ CExtend

CSpec ==
    /\ CInit
    /\ [][CNext]_cvars
    /\ WF_cvars(CHeat)
    /\ WF_cvars(CCool)
    /\ WF_cvars(CAnneal)
    /\ WF_cvars(CExtend)

CPrimerNonIncreasingTotal ==
    primer + hybrid + dna + template >= 0
=======================================================================