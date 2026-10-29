---------------------------- MODULE IntegerDivision ----------------------------
(***************************************************************************)
(* Integer division by repeated subtraction (non-negative dividend) or     *)
(* repeated addition (negative dividend) of a positive divisor.            *)
(* On termination:  dividend = quotient * divisor + remainder              *)
(*                  0 <= remainder < |divisor|                             *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS Dividends,   \* set of dividends to test (negative and positive)
          Divisors     \* set of divisors to test (positive integers)

ASSUME DividendsAssumption == Dividends \subseteq Int
ASSUME DivisorsAssumption  == /\ Divisors \subseteq Nat
                              /\ 0 \notin Divisors

VARIABLES dividend,   \* the input dividend
          divisor,    \* the input divisor
          quotient,   \* the computed quotient
          remainder,  \* the computed remainder (working value)
          pc          \* control state: "loop" or "done"

vars == <<dividend, divisor, quotient, remainder, pc>>

Abs(n) == IF n < 0 THEN -n ELSE n

-----------------------------------------------------------------------------

TypeOK ==
    /\ dividend \in Dividends
    /\ divisor \in Divisors
    /\ quotient \in Int
    /\ remainder \in Int
    /\ pc \in {"loop", "done"}

Init ==
    /\ dividend \in Dividends
    /\ divisor \in Divisors
    /\ quotient = 0
    /\ remainder = dividend
    /\ pc = "loop"

(* Positive (or zero) working value still too large: subtract divisor *)
Subtract ==
    /\ pc = "loop"
    /\ remainder >= divisor
    /\ remainder' = remainder - divisor
    /\ quotient' = quotient + 1
    /\ UNCHANGED <<dividend, divisor, pc>>

(* Negative working value: add divisor *)
Add ==
    /\ pc = "loop"
    /\ remainder < 0
    /\ remainder' = remainder + divisor
    /\ quotient' = quotient - 1
    /\ UNCHANGED <<dividend, divisor, pc>>

(* Remainder within bounds: terminate *)
Finish ==
    /\ pc = "loop"
    /\ 0 <= remainder
    /\ remainder < divisor
    /\ pc' = "done"
    /\ UNCHANGED <<dividend, divisor, quotient, remainder>>

(* Terminal state: stutter to avoid deadlock *)
Terminated ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Subtract \/ Add \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety properties *)

\* Loop invariant: the division equation holds at every step
LoopInvariant == dividend = quotient * divisor + remainder

\* Division correctness upon termination
DivisionCorrectness ==
    pc = "done" => dividend = quotient * divisor + remainder

\* Remainder bounds upon termination
RemainderBounds ==
    pc = "done" => (0 <= remainder /\ remainder < Abs(divisor))

\* Sign handling: negative dividends yield negative quotients,
\* non-negative dividends yield non-negative quotients
SignHandling ==
    pc = "done" =>
        /\ (dividend < 0 => quotient < 0)
        /\ (dividend >= 0 => quotient >= 0)

\* Agreement with the built-in (floored) division and modulus
MatchesBuiltin ==
    pc = "done" =>
        /\ quotient = dividend \div divisor
        /\ remainder = dividend % divisor

Correctness ==
    /\ TypeOK
    /\ LoopInvariant
    /\ DivisionCorrectness
    /\ RemainderBounds
    /\ SignHandling
    /\ MatchesBuiltin

-----------------------------------------------------------------------------
(* Liveness *)

Termination == <>(pc = "done")

THEOREM Spec => []Correctness
THEOREM Spec => Termination
=============================================================================