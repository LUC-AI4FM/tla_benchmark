------------------------------ MODULE UnchangedTest ------------------------------
(***************************************************************************)
(* Test harness for the semantics of the TLA+ UNCHANGED operator.          *)
(*                                                                         *)
(* State: an array-like function x over 1..N and a scalar y.               *)
(*                                                                         *)
(*   - SameStep keeps the whole state the same and checks that UNCHANGED   *)
(*     is TRUE for many expressions derived from the state.                *)
(*   - SwapStep swaps two array elements and toggles y. It then checks     *)
(*     that UNCHANGED is TRUE for expressions whose VALUE does not change, *)
(*     even though the variables they mention do change.                   *)
(*                                                                         *)
(* Each check prints a message when it passes. A failed check stops TLC    *)
(* with an assertion error.                                                *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 3

VARIABLES x, y

vars == <<x, y>>

(* Assert the condition, then print a success message for the test case. *)
Check(cond, name) ==
    /\ Assert(cond, <<"UNCHANGED test FAILED:", name>>)
    /\ PrintT(<<"UNCHANGED test passed:", name>>)

Init ==
    /\ x = [i \in 1..N |-> i]
    /\ y = 0

---------------------------------------------------------------------------------
(* Case A: the whole state stays the same. *)
SameStep ==
    /\ x' = x
    /\ y' = y
    /\ Check(x[1]' = x[1],                                  "A1: primed equality on element")
    /\ Check(UNCHANGED (x[1]),                              "A2: UNCHANGED on element")
    /\ Check(UNCHANGED [a |-> x[1], b |-> x[2]],            "A3: record built from array")
    /\ Check(UNCHANGED (\E i \in DOMAIN x : x[i] = 2),      "A4: existential quantifier")
    /\ Check(UNCHANGED (\A i \in DOMAIN x : x[i] > 0),      "A5: universal quantifier")
    /\ Check(UNCHANGED (CHOOSE i \in DOMAIN x : x[i] = 2),  "A6: CHOOSE over array")
    /\ Check(UNCHANGED {x[i] + 1 : i \in DOMAIN x},         "A7: set map over indices")
    /\ Check(UNCHANGED {i \in DOMAIN x : x[i] > 1},         "A8: filtered set comprehension")
    /\ Check(UNCHANGED (DOMAIN x),                          "A9: domain of array")
    /\ Check(UNCHANGED {x},                                 "A10: set containing array")
    /\ Check(UNCHANGED {0, x[1], y, 42},                    "A11: mixed constants and state")
    /\ Check(UNCHANGED <<x, y>>,                            "A12: whole state tuple")

(* Case B: x[1] and x[2] are swapped and y toggles. UNCHANGED is applied  *)
(* to expressions whose values are still the same.                         *)
SwapStep ==
    /\ x' = [x EXCEPT ![1] = x[2], ![2] = x[1]]
    /\ y' = 1 - y
    /\ Check(x[3]' = x[3],                                  "B1: primed equality on untouched element")
    /\ Check(UNCHANGED (x[3]),                              "B2: UNCHANGED on untouched element")
    /\ Check(UNCHANGED [a |-> x[3], b |-> x[1] + x[2]],     "B3: record with invariant values")
    /\ Check(UNCHANGED (\E i \in DOMAIN x : x[i] = y + 1 \/ x[i] = 2 - y \/ x[i] = 1),
                                                            "B4: existential quantifier")
    /\ Check(UNCHANGED (\A i \in DOMAIN x : x[i] \in 1..N), "B5: universal quantifier")
    /\ Check(UNCHANGED (CHOOSE v \in {x[i] : i \in DOMAIN x} : v = 3),
                                                            "B6: CHOOSE over array values")
    /\ Check(UNCHANGED {x[i] : i \in DOMAIN x},             "B7: set map over indices")
    /\ Check(UNCHANGED {i \in DOMAIN x : x[i] > 2},         "B8: filtered set comprehension")
    /\ Check(UNCHANGED (DOMAIN x),                          "B9: domain of array")
    /\ Check(UNCHANGED {x[i] : i \in {1, 2}},               "B10: set of swapped elements")
    /\ Check(UNCHANGED {0, x[1], x[2], 1},                  "B11: mixed constants and state")
    /\ Check(UNCHANGED {y, 1 - y},                          "B12: set of toggling scalar")
    /\ Check(~ UNCHANGED x,                                 "B13: whole array actually changes")
    /\ Check(~ UNCHANGED y,                                 "B14: scalar actually changes")

Next == SameStep \/ SwapStep

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

---------------------------------------------------------------------------------
(* Trivial invariant: the real check is that no assertion fails. *)
Inv == TRUE

TypeOK ==
    /\ x \in [1..N -> 1..N]
    /\ y \in {0, 1}

=================================================================================