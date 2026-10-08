----------------------------- MODULE EvenOdd -----------------------------

EXTENDS Naturals, TLC

(*
  A simple TLA+ model of mutually recursive procedures Even and Odd.
  Even(n) = if n = 0 then TRUE else Odd(n - 1)
  Odd(n)  = if n = 0 then FALSE else Even(n - 1)

  The main program invokes Even on N and produces a boolean result.
  For the concrete test N = 6, the system counts:
    - how many times Odd is entered (oddEntries),
    - how many Even->Odd calls occur (eoCalls).
  Both must be exactly 3 when the computation terminates.
*)

N == 6

CONSTANTS  (* none *)

VARIABLES pc, arg, res, oddEntries, eoCalls

Vars == << pc, arg, res, oddEntries, eoCalls >>

TypeOK ==
  /\ pc \in {"Even", "Odd", "Done"}
  /\ arg \in Nat
  /\ res \in BOOLEAN \cup {"NotSet"}
  /\ oddEntries \in Nat
  /\ eoCalls \in Nat

Init ==
  /\ pc = "Even"
  /\ arg = N
  /\ res = "NotSet"
  /\ oddEntries = 0
  /\ eoCalls = 0
  /\ TypeOK

(*
  NonStutter captures all computational (non-stuttering) steps.
  - EvenZero: Even(0) returns TRUE and halts.
  - EvenRecur: Even(n>0) calls Odd(n-1); count Odd entry and Even->Odd call.
  - OddZero: Odd(0) returns FALSE and halts.
  - OddRecur: Odd(n>0) calls Even(n-1).
*)
NonStutter ==
  \/ /\ pc = "Even" /\ arg = 0
     /\ pc' = "Done"
     /\ arg' = arg
     /\ res' = TRUE
     /\ UNCHANGED << oddEntries, eoCalls >>
  \/ /\ pc = "Even" /\ arg > 0
     /\ pc' = "Odd"
     /\ arg' = arg - 1
     /\ oddEntries' = oddEntries + 1
     /\ eoCalls' = eoCalls + 1
     /\ res' = res
  \/ /\ pc = "Odd" /\ arg = 0
     /\ pc' = "Done"
     /\ arg' = arg
     /\ res' = FALSE
     /\ UNCHANGED << oddEntries, eoCalls >>
  \/ /\ pc = "Odd" /\ arg > 0
     /\ pc' = "Even"
     /\ arg' = arg - 1
     /\ UNCHANGED << res, oddEntries, eoCalls >>

Next ==
  NonStutter
  \/ /\ pc = "Done" /\ UNCHANGED Vars

Spec ==
  Init /\ [][Next]_Vars /\ WF_Vars(NonStutter)

(*
  Liveness property: the computation eventually completes.
*)
Termination == <> (pc = "Done")

(*
  Optional safety property that can be checked by TLC:
  For N = 6, across all reachable states counts never exceed 3,
  and at termination they are exactly 3.
*)
CountsOK ==
  /\ oddEntries <= 3 /\ eoCalls <= 3
  /\ (pc = "Done" => /\ oddEntries = 3 /\ eoCalls = 3)

============================================================================