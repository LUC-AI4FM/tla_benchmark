------------------------------ MODULE EvenOdd ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT N \in Nat

VARIABLES pc, result, stack, oddCount, xEven, xOdd

(* ------------------------------------------------------------------ *)
(* Frame type for the explicit call stack *)
Frame == [proc: {"Even","Odd"}, arg: Nat]

(* ------------------------------------------------------------------ *)
(* Initial state *)
Init ==
  /\ stack = <<[proc |-> "Even", arg |-> N]>>
  /\ pc = "Even"
  /\ result = FALSE
  /\ oddCount = 0
  /\ xEven = N
  /\ xOdd = 0

(* ------------------------------------------------------------------ *)
(* Auxiliary predicates *)
InOdd == pc = "Odd"

CallOdd == pc = "Odd" /\ oddCount > 0

/* _POSSIBLE InOdd */
/* _POSSIBLE CallOdd */

(* ------------------------------------------------------------------ *)
(* Transition relation *)
Next ==
  LET top == Head(stack)
      rest == Tail(stack)
  IN
    \/ (* Even case with base argument 0 *)
       /\ pc = "Even"
       /\ top.proc = "Even"
       /\ top.arg = 0
       /\ stack' = rest
       /\ result' = TRUE
       /\ oddCount' = oddCount
       /\ xEven' = 0
       /\ xOdd' = 0
       /\ pc' = IF Len(rest) = 0 THEN "Done" ELSE Head(rest).proc

    \/ (* Odd case with base argument 0 *)
       /\ pc = "Odd"
       /\ top.proc = "Odd"
       /\ top.arg = 0
       /\ stack' = rest
       /\ result' = FALSE
       /\ oddCount' = oddCount
       /\ xEven' = 0
       /\ xOdd' = 0
       /\ pc' = IF Len(rest) = 0 THEN "Done" ELSE Head(rest).proc

    \/ (* Even case with argument > 0: call Odd *)
       /\ pc = "Even"
       /\ top.proc = "Even"
       /\ top.arg > 0
       /\ stack' = <<[proc |-> "Odd", arg |-> top.arg - 1]>> ++ rest
       /\ result' = result
       /\ oddCount' = oddCount + 1
       /\ xEven' = top.arg
       /\ xOdd' = top.arg - 1
       /\ pc' = "Odd"

    \/ (* Odd case with argument > 0: call Even *)
       /\ pc = "Odd"
       /\ top.proc = "Odd"
       /\ top.arg > 0
       /\ stack' = <<[proc |-> "Even", arg |-> top.arg - 1]>> ++ rest
       /\ result' = result
       /\ oddCount' = oddCount
       /\ xEven' = top.arg - 1
       /\ xOdd' = top.arg
       /\ pc' = "Even"

(* ------------------------------------------------------------------ *)
(* Liveness property: termination *)
Termination == <> (pc = "Done")

(* ------------------------------------------------------------------ *)
(* Postcondition on the number of Odd calls observed *)
PossibleCounts == oddCount = 3

(* ------------------------------------------------------------------ *)
vars == {pc, result, stack, oddCount, xEven, xOdd}

Spec ==
  Init
  /\ [][Next]_vars
  /\ WF_vars(Next)
  /\ Termination
  /\ PossibleCounts

=============================================================================