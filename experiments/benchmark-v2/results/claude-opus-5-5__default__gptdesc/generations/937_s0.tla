--------------------------- MODULE HourClock2 ---------------------------
(***************************************************************************)
(* The hour clock of module HourClock, augmented with a liveness           *)
(* requirement. The definitions of HourClock (HCini, HCnxt, HC) are        *)
(* restated here so that the module parses on its own.                     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

VARIABLE hr

-----------------------------------------------------------------------------
(* Inherited hour clock specification (from HourClock)                     *)

HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

-----------------------------------------------------------------------------
(* Live hour clock specification                                           *)

Init == HCini

Next == HCnxt

LSpec == HC /\ WF_hr(HCnxt)

Spec == LSpec

-----------------------------------------------------------------------------
(* Properties                                                              *)

\* The clock ticks infinitely often.
AlwaysTick == []<><<HCnxt>>_hr

\* Every hour value from 1 through 12 recurs infinitely often.
AllTimes == \A n \in 1 .. 12 : []<>(hr = n)

\* The initial-state typing condition remains always true.
TypeCorrect == []HCini

\* Safety invariant (state predicate form of TypeCorrect).
TypeInvariant == HCini

THEOREM LSpec => AlwaysTick /\ AllTimes /\ TypeCorrect

-----------------------------------------------------------------------------
(* Settling property, which LSpec does NOT satisfy: the clock eventually   *)
(* stays at a single hour forever.                                         *)

Settle == \E n \in 1 .. 12 : <>[](hr = n)

(***************************************************************************)
(* Postcondition: the structure of a counterexample to Settle.  Any        *)
(* counterexample produced by checking Settle against LSpec is a lasso      *)
(* behavior: a finite (possibly empty) stem followed by a loop that runs   *)
(* through all twelve hour values in order, each step being an HCnxt step. *)
(***************************************************************************)
IsHCStep(s, t) == t = IF s # 12 THEN s + 1 ELSE 1

IsLassoCounterExample(stem, loop) ==
  /\ Len(loop) = 12
  /\ \A i \in 1 .. Len(stem) : stem[i] \in 1 .. 12
  /\ \A i \in 1 .. Len(loop) : loop[i] \in 1 .. 12
  /\ \A i \in 1 .. (Len(stem) - 1) : IsHCStep(stem[i], stem[i + 1])
  /\ Len(stem) > 0 => IsHCStep(stem[Len(stem)], loop[1])
  /\ \A i \in 1 .. 11 : IsHCStep(loop[i], loop[i + 1])
  /\ IsHCStep(loop[12], loop[1])
  /\ \A n \in 1 .. 12 : \E i \in 1 .. 12 : loop[i] = n

PostCondition ==
  \A s \in 1 .. 12 :
    \E loop \in [1 .. 12 -> 1 .. 12] :
      /\ loop[1] = s
      /\ IsLassoCounterExample(<<>>, loop)

=============================================================================