------------------------------ MODULE FingerprintNormalization ------------------------------
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(* Test harness for checking that TLC fingerprints equal values equally,   *)
(* even when they are written with duplicate elements, in a different      *)
(* element order, or with record fields in a different order.              *)
(*                                                                         *)
(* x : a function from {1,2} into SUBSET Int.                              *)
(* y : a function from {1,2} into SUBSET of records [a, b].                *)
(*                                                                         *)
(* Every transition assigns a value that is written differently but is     *)
(* mathematically equal to the current one. So no new distinct state       *)
(* should appear. The number of distinct states found must equal the       *)
(* number of distinct initial states.                                      *)
(***************************************************************************)

CONSTANTS Dom          \* Domain of the functions, e.g. {1, 2}

ASSUME Dom = {1, 2}

VARIABLES x, y

vars == <<x, y>>

\* Baseline values, written in normalized form.
IntVals == { {2, 3, 4}, {2} }

RecA == [a |-> {1, 2}, b |-> 1]
RecB == [a |-> {3},    b |-> 2]

RecVals == { {RecA, RecB}, {RecA}, {} }

Rec == [a : SUBSET {1, 2, 3}, b : {1, 2}]

\* The set of all initial states. It is used to check that no new state is
\* reached.
InitStates == [Dom -> IntVals] \X [Dom -> RecVals]

NumInitStates == Cardinality(InitStates)

(***************************************************************************)
(* Static sanity checks on equality. These hold if and only if the         *)
(* evaluator normalizes the values correctly.                              *)
(***************************************************************************)
ASSUME Assert({2, 2} = {2}, "Set normalization failed: {2,2} # {2}")
ASSUME Assert({4, 4, 3} = {3, 4}, "Set normalization failed: {4,4,3} # {3,4}")
ASSUME Assert({4, 3, 2} = {2, 3, 4}, "Set ordering failed: {4,3,2} # {2,3,4}")
ASSUME Assert([b |-> 1, a |-> {2, 1, 1}] = RecA,
              "Record normalization failed: [b|->1, a|->{2,1,1}] # RecA")
ASSUME Assert({RecB, RecA, RecA} = {RecA, RecB},
              "Set-of-records normalization failed")

TypeOK ==
    /\ x \in [Dom -> SUBSET {2, 3, 4}]
    /\ y \in [Dom -> SUBSET Rec]

Init ==
    /\ x \in [Dom -> IntVals]
    /\ y \in [Dom -> RecVals]

(***************************************************************************)
(* Rewrite of an integer set, with duplicates and a different order.       *)
(***************************************************************************)
RewriteInt(s) ==
    IF s = {2} THEN {2, 2}
    ELSE IF s = {2, 3, 4} THEN {4, 4, 3, 2, 3}
    ELSE s

(***************************************************************************)
(* Rewrite of a record set, with duplicated elements, permuted fields, and *)
(* duplicate values inside the field definitions.                          *)
(***************************************************************************)
RewriteRec(s) ==
    IF s = {RecA, RecB}
        THEN { [b |-> 2, a |-> {3, 3}],
               [b |-> 1, a |-> {2, 1, 1}],
               [a |-> {1, 2, 2}, b |-> 1] }
    ELSE IF s = {RecA}
        THEN { [b |-> 1, a |-> {2, 2, 1}], [a |-> {1, 2}, b |-> 1] }
    ELSE s

\* Rewrite one entry of x with duplicates and reordering.
RewriteX(i) ==
    /\ x' = [x EXCEPT ![i] = RewriteInt(x[i])]
    /\ Assert(x' = x, "Fingerprint failure: rewritten integer set differs")
    /\ UNCHANGED y

\* Rebuild x, listing the domain in a different order.
RebuildX ==
    /\ x' = [i \in {2, 1, 2} |-> RewriteInt(x[i])]
    /\ Assert(x' = x, "Fingerprint failure: rebuilt function x differs")
    /\ UNCHANGED y

\* Rewrite one entry of y, with record fields permuted and duplicated.
RewriteY(i) ==
    /\ y' = [y EXCEPT ![i] = RewriteRec(y[i])]
    /\ Assert(y' = y, "Fingerprint failure: rewritten record set differs")
    /\ UNCHANGED x

\* Rewrite both at once.
RewriteBoth ==
    /\ x' = [i \in {2, 1} |-> RewriteInt(x[i])]
    /\ y' = [i \in {1, 1, 2} |-> RewriteRec(y[i])]
    /\ Assert(<<x', y'>> = <<x, y>>,
              "Fingerprint failure: combined rewrite differs")

Next ==
    \/ \E i \in Dom : RewriteX(i)
    \/ RebuildX
    \/ \E i \in Dom : RewriteY(i)
    \/ RewriteBoth

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)

\* Every reachable state is one of the initial states. So the number of
\* distinct states equals the number of distinct initial states.
OnlyInitStates == <<x, y>> \in InitStates

\* Values stay normalized and equal to their rewritten forms.
NormalizationInv ==
    /\ \A i \in Dom : RewriteInt(x[i]) = x[i]
    /\ \A i \in Dom : RewriteRec(y[i]) = y[i]

\* Check of the distinct-state count, done through TLC's statistics.
\* TLCGet("distinct") must never exceed the number of initial states.
StateCountInv ==
    Assert(TLCGet("distinct") <= NumInitStates,
           "State count failure: more distinct states than initial states")

(***************************************************************************)
(* Temporal properties                                                     *)
(***************************************************************************)

\* The values never change: every step is a stuttering step semantically.
Stable == [][<<x, y>> = <<x', y'>>]_vars

\* The state always remains one of the initial states.
AlwaysInit == []OnlyInitStates

THEOREM Spec => [](TypeOK /\ OnlyInitStates /\ NormalizationInv)
==========================================================================================