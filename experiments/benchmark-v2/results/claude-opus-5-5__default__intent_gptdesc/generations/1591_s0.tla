---------------------------- MODULE RecursiveParity ----------------------------
(***************************************************************************)
(* A model of a mutually recursive parity check:                            *)
(*                                                                         *)
(*   procedure IsEven(n): if n = 0 then result := TRUE                     *)
(*                        else call IsOdd(n-1); return                     *)
(*   procedure IsOdd(n):  if n = 0 then result := FALSE                    *)
(*                        else call IsEven(n-1); return                    *)
(*                                                                         *)
(*   main: call IsEven(N); final := result                                 *)
(*                                                                         *)
(* Calls and returns use an explicit stack of frames. Each frame records   *)
(* the return location and the caller's saved local argument.              *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT N

ASSUME NAssumption == N \in Nat

VARIABLES
    pc,      \* current control location
    n,       \* local argument of the active procedure
    stack,   \* call stack: sequence of frames [ret, n], Head = most recent
    result,  \* boolean result register written by the base cases
    final    \* final boolean computed by main

vars == <<pc, n, stack, result, final>>

Labels    == {"Start", "E1", "O1", "ERet", "ORet", "Fin", "Done"}
RetLabels == {"Fin", "ERet", "ORet"}
Frame     == [ret : RetLabels, n : Nat]

IsEvenNum(x) == x % 2 = 0

----------------------------------------------------------------------------
(* Helper: return from the active procedure (atomic pop + restore)         *)
Return ==
    /\ stack # << >>
    /\ pc'    = Head(stack).ret
    /\ n'     = Head(stack).n
    /\ stack' = Tail(stack)

----------------------------------------------------------------------------
Init ==
    /\ pc     = "Start"
    /\ n      = 0
    /\ stack  = << >>
    /\ result = FALSE
    /\ final  = FALSE

(* main: call IsEven(N) *)
Start ==
    /\ pc = "Start"
    /\ stack' = << [ret |-> "Fin", n |-> n] >> \o stack
    /\ n'     = N
    /\ pc'    = "E1"
    /\ UNCHANGED <<result, final>>

(* body of IsEven *)
E1 ==
    /\ pc = "E1"
    /\ IF n = 0
         THEN /\ result' = TRUE
              /\ Return
         ELSE /\ stack' = << [ret |-> "ERet", n |-> n] >> \o stack
              /\ n'     = n - 1
              /\ pc'    = "O1"
              /\ UNCHANGED result
    /\ UNCHANGED final

(* IsEven: return after the recursive call to IsOdd completes *)
ERet ==
    /\ pc = "ERet"
    /\ Return
    /\ UNCHANGED <<result, final>>

(* body of IsOdd *)
O1 ==
    /\ pc = "O1"
    /\ IF n = 0
         THEN /\ result' = FALSE
              /\ Return
         ELSE /\ stack' = << [ret |-> "ORet", n |-> n] >> \o stack
              /\ n'     = n - 1
              /\ pc'    = "E1"
              /\ UNCHANGED result
    /\ UNCHANGED final

(* IsOdd: return after the recursive call to IsEven completes *)
ORet ==
    /\ pc = "ORet"
    /\ Return
    /\ UNCHANGED <<result, final>>

(* main: record final result *)
Fin ==
    /\ pc = "Fin"
    /\ final' = result
    /\ pc'    = "Done"
    /\ UNCHANGED <<n, stack, result>>

(* Terminated: stutter to avoid deadlock *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Start \/ E1 \/ ERet \/ O1 \/ ORet \/ Fin \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ pc \in Labels
    /\ n \in Nat
    /\ stack \in Seq(Frame)
    /\ result \in BOOLEAN
    /\ final \in BOOLEAN

(* Stack depth is bounded by the recursion depth determined by N *)
StackBounded == Len(stack) <= N + 1

(* Stack safety: every stored frame (return location and saved argument)  *)
(* is exactly what was pushed at that depth; nothing is ever corrupted.   *)
(* k = distance from the bottom of the stack.                             *)
StackIntegrity ==
    \A i \in 1..Len(stack) :
        LET k == Len(stack) - i IN
          IF k = 0
            THEN stack[i] = [ret |-> "Fin", n |-> 0]
            ELSE stack[i] = [ret |-> IF k % 2 = 1 THEN "ERet" ELSE "ORet",
                             n   |-> N - (k - 1)]

(* The active procedure's argument matches its depth, and the active      *)
(* procedure (IsEven / IsOdd) alternates correctly with depth.            *)
ActiveFrameOK ==
    pc \in {"E1", "O1", "ERet", "ORet"} =>
        /\ Len(stack) >= 1
        /\ Len(stack) <= N + 1
        /\ n = N - (Len(stack) - 1)
        /\ (pc \in {"E1", "ERet"} <=> Len(stack) % 2 = 1)

(* Partial correctness at return points: after the nested call returns,  *)
(* result holds the correct parity of the current procedure's argument.  *)
ReturnCorrect ==
    /\ pc = "ERet" => result = IsEvenNum(n)
    /\ pc = "ORet" => result = ~IsEvenNum(n)

(* Before the call or after it, main has no active procedure frames *)
MainFrameOK ==
    pc \in {"Start", "Fin", "Done"} => stack = << >>

(* Functional correctness *)
FinCorrect  == pc = "Fin"  => result = IsEvenNum(N)
DoneCorrect == pc = "Done" => /\ final = IsEvenNum(N)
                              /\ result = IsEvenNum(N)
                              /\ stack = << >>

Inv ==
    /\ TypeOK
    /\ StackBounded
    /\ StackIntegrity
    /\ ActiveFrameOK
    /\ ReturnCorrect
    /\ MainFrameOK
    /\ FinCorrect
    /\ DoneCorrect

(* Once terminated, the result is stable forever *)
FinalStable ==
    [][pc = "Done" => (pc' = "Done" /\ UNCHANGED <<final, result, stack, n>>)]_vars

----------------------------------------------------------------------------
(* Liveness *)

Termination == <>(pc = "Done")

EventuallyCorrect ==
    <>[](pc = "Done" /\ stack = << >> /\ final = IsEvenNum(N))

CallsEventuallyReturn ==
    (pc = "E1" \/ pc = "O1") ~> (pc = "Fin")

THEOREM Spec => []Inv
THEOREM Spec => FinalStable
THEOREM Spec => Termination /\ EventuallyCorrect /\ CallsEventuallyReturn
=============================================================================