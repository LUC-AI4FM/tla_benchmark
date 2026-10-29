---------------------------- MODULE PrimeParamTest ----------------------------
EXTENDS Naturals

VARIABLES arr, x, last

vars == <<arr, x, last>>

Idx == {1, 2}

(* Parameterized update: the element is set to whatever expression is passed. *)
SetElem(i, p) == arr' = [arr EXCEPT ![i] = p]

(* Parameterized update that primes its parameter inside the definition.     *)
(* Priming applies at the point of use, so SetElemPrimed(i, x) uses x'.      *)
SetElemPrimed(i, p) == arr' = [arr EXCEPT ![i] = p']

Init ==
    /\ arr = [i \in Idx |-> 0]
    /\ x = 0
    /\ last = "None"

(* Transition Type A: element gets the next-state value of x *)
TypeA ==
    /\ x' = x + 1
    /\ SetElem(1, x')
    /\ last' = "A"

(* Transition Type B: element gets the current-state value of x *)
TypeB ==
    /\ x' = x + 1
    /\ SetElem(1, x)
    /\ last' = "B"

(* Transition Type C: priming inside the definition, unprimed at use site *)
TypeC ==
    /\ x' = x + 1
    /\ SetElemPrimed(2, x)
    /\ last' = "C"

Next == TypeA \/ TypeB \/ TypeC

Spec == Init /\ [][Next]_vars

Constraint == x < 6

TypeOK ==
    /\ arr \in [Idx -> Nat]
    /\ x \in Nat
    /\ last \in {"None", "A", "B", "C"}

Inv ==
    /\ TypeOK
    /\ (last = "A") => (arr[1] = x)
    /\ (last = "B") => (arr[1] = x - 1 /\ arr[1] # x)
    /\ (last = "C") => (arr[2] = x)
=============================================================================